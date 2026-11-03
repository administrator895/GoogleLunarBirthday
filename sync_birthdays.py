#!/usr/bin/env python3

import hashlib
import os
import re
import sys
import urllib.parse
from datetime import date, datetime, time, timedelta, timezone

import caldav
import vobject
from caldav.lib.error import AuthorizationError
from icalendar import Calendar, Component, Event

import lunardate

import config

# ---- 常量 ----

# 日历用 www.google.com 这个旧端点，它是唯一仍接受应用专用密码的；
# 新端点 apidata.googleusercontent.com/caldav/v2 只认 OAuth。
CARDDAV = "https://www.googleapis.com/carddav/v1/principals/{}/"
DAV_ROOT = "https://www.google.com/calendar/dav/{}/"

XML = '<?xml version="1.0" encoding="utf-8"?>'
PROPFIND = {"Depth": "1", "Content-Type": 'application/xml; charset="utf-8"'}


# ---- 错误码 ----

# 错误码 → 含义。所有报错统一为「[E00x] 谁：哪一项：原值」，便于在 Actions 日志里搜。
ERRORS = {
    "E001": "缺少环境变量",
    "E002": "Google 认证失败",
    "E003": "通讯录返回 0 张卡片",
    "E004": "找不到目标日历",
    "E005": "卡片解析失败",
    "E006": "农历标签没有填日期",
    "E007": "日期格式无法识别",
    "E008": "月份超出 1-12",
    "E009": "日期超出 1-30",
    "E010": "农历日期无法换算",
    "E011": "事件写入失败",
    "E012": "事件删除失败",
    "E013": "有农历生日但没有任何姓名",
}


def err(code, msg):
    """拼一条带错误码的消息。"""
    return f"[{code}] {msg}"


def code_of(line):
    """从一条错误消息里取出错误码，用于结尾按码汇总。"""
    m = re.match(r"\[(E\d{3})\]", line)
    return m.group(1) if m else ""


class BirthdayError(Exception):
    """通讯录里某条数据不可用。带上错误码，由 main 收集成清单统一退出。"""

    def __init__(self, code, msg):
        super().__init__(err(code, msg))


# ---- 通讯录 ----

def kids(elem, name):
    """按标签的本地名取出所有匹配元素，忽略命名空间前缀。

    DAV 响应里的标签是 {DAV:}response 这种形式，且前缀不保证一致，所以剥掉 {…} 只比后半段。
    """
    return [e for e in elem.iter() if e.tag.rsplit("}", 1)[-1] == name]


def fetch_cards(client, email):
    """取回全部 vCard 原文，返回 [(卡片文件名, 原文)]。

    Google 对 REPORT addressbook-query 一律返回 400，只能拆成三次 PROPFIND 加逐条 GET：
    principal → 通讯录根目录 → 地址簿 → 条目。
    """
    # principal → 通讯录根目录。要先定位 addressbook-home-set 再取它的 href，
    # 直接取第一个 href 拿到的是 principal 自身。
    base = CARDDAV.format(urllib.parse.quote(email))
    body = XML + ('<d:propfind xmlns:d="DAV:" xmlns:c="urn:ietf:params:xml:ns:carddav">'
                  '<d:prop><c:addressbook-home-set/></d:prop></d:propfind>')
    tree = client.request(base, "PROPFIND", body, {**PROPFIND, "Depth": "0"}).tree
    home = urllib.parse.urljoin(base, kids(kids(tree, "addressbook-home-set")[0], "href")[0].text)

    # 根目录 → 具体地址簿，排除根目录自身
    body = XML + '<d:propfind xmlns:d="DAV:"><d:prop><d:resourcetype/><d:getetag/></d:prop></d:propfind>'
    listing = client.request(home, "PROPFIND", body, PROPFIND).tree
    book = None
    for r in kids(listing, "response"):
        if not kids(r, "collection"):
            continue
        href = urllib.parse.urljoin(home, kids(r, "href")[0].text)
        if href.rstrip("/") != home.rstrip("/"):
            book = href
            break
    book = book or home.rstrip("/") + "/default/"  # 兜底，Google 的默认地址簿叫 default

    # 地址簿 → 条目，逐条取原文
    cards = []
    for r in kids(client.request(book, "PROPFIND", body, PROPFIND).tree, "response"):
        href = urllib.parse.urljoin(book, kids(r, "href")[0].text)
        if href.rstrip("/") == book.rstrip("/"):
            continue
        cards.append((href.rstrip("/").rsplit("/", 1)[-1], client.request(href, "GET").raw))
    return cards


# ---- 解析 vCard ----

CJK = re.compile(r"[\u4e00-\u9fff]")


def text_of(v, name):
    """取一个属性的文本值，没有则返回空字符串。

    vobject 的 contents 键大小写不固定（标准属性存小写），所以两种写法都试。
    """
    for key in (name.lower(), name.upper()):
        el = v.contents.get(key)
        if el:
            return str(el[0].value or "").strip()
    return ""


def display_name(v):
    """按「名（FN）→ 姓名（N）→ 昵称」取一个能用的名字，全空返回空串。

    Google 通讯录的三个姓名框分别落在 FN、N、NICKNAME 上，只填其中一两个是常态，
    所以逐级回退。空字符串交给调用方判断——只有真的存在农历生日时缺名字才算错误。
    """
    fn = text_of(v, "fn")
    if fn:
        return fn

    n = getattr(v, "n", None)
    if n:
        family = str(n.value.family or "").strip()
        given = str(n.value.given or "").strip()
        if family or given:
            # 中文按「姓+名」，其余按「名 姓」，否则中文名会拼成「三张」
            return family + given if CJK.search(family + given) \
                else " ".join(x for x in (given, family) if x)

    return text_of(v, "nickname")


def lunar_birthdays(v, who=""):
    """从一张 vCard 里找出农历生日，逐个产出 (月, 日)。

    Google 把「自定义日期」存成带分组前缀的一对属性，必须按 itemN 配对后看标签：
      item1.X-ABDATE:1990-08-15   ← 日期本体，年份是出生年
      item1.X-ABLABEL:农历生日     ← 用户手输的标签
    vobject 解析后把前缀放进 child.group，正好用来聚合。

    解析失败抛 BirthdayError，由调用方收集成失败清单，不静默跳过。
    """
    groups = {}
    for child in v.getChildren():
        group = getattr(child, "group", None)
        if group:
            groups.setdefault(group, {})[child.name.upper()] = child

    for props in groups.values():
        label_el = props.get("X-ABLABEL")
        label = str(label_el.value) if label_el else ""
        if not any(t in label for t in config.LUNAR_LABELS):
            continue
        date_el = props.get("X-ABDATE") or props.get("BDAY")
        if date_el is None:
            raise BirthdayError("E006", f"{who}：标签「{label}」只有名称、没有填日期")
        yield parse_lunar_month_day(date_el, who, label)


def parse_lunar_month_day(el, who="", label=""):
    """从 X-ABDATE 取出 (月, 日)，年份丢弃不用。
    """
    raw = str(el.value).strip()
    m = re.match(r"^(?:(\d{4})-|-{2})(\d{1,2})-(\d{1,2})", raw)
    if not m:
        raise BirthdayError("E007", f"{who}：标签「{label}」的日期格式无法识别（{raw}）")

    month, day = int(m.group(2)), int(m.group(3))
    if not 1 <= month <= 12:
        raise BirthdayError(
            "E008", f"{who}：标签「{label}」的月份是 {month}，农历只有 1-12 月（{raw}）")
    if not 1 <= day <= 30:
        # 这个字段按公历校验，31 号能填进去，但农历每月最多 30 天
        raise BirthdayError(
            "E009", f"{who}：标签「{label}」的日期是 {day} 号，农历每月最多 30 天（{raw}）")
    return month, day


# ---- 换算 ----

def to_solar(year, month, day, leap=False):
    """把农历日期换算成公历 date，leap=True 表示闰月。

    小月只有 29 天，三十日的生日在那种年份按廿九过；这是唯一的回退，属于民俗处理。
    除此之外换算不出来就是数据有问题，抛 ValueError 让调用方报错。
    """
    for dd in ([day, 29] if day == 30 else [day]):
        try:
            return lunardate.LunarDate(year, month, dd, leap).to_solar_date()
        except ValueError:
            continue
    raise ValueError(err("E010", f"农历 {year} 年{'闰' if leap else ''}{month} 月 {day} 日不存在"))


def lunar_dates(year, month, day):
    """产出一年的公历日期，元素为 (日期, 是否闰月)。

    闰月年生日过两次：正常月一次、闰月再一次。哪年多一次只看当年历法，与标签无关。
    """
    dates = [(to_solar(year, month, day), False)]
    if lunardate.LunarDate.leap_month_for_year(year) == month:
        dates.append((to_solar(year, month, day, leap=True), True))
    return dates


# ---- 事件生成 ----

# 事件格式版本，参与 UID 计算。只有想让日历里的条目全部重建、重写时才 +1：
# 常规的字段增减、文案调整都由 sig() 自动识别并就地更新，不必动它。
SCHEMA = 1


def build_events(cards):
    """把通讯录算成「日历里应该存在的事件全集」，返回 (events, errors)。

    events 是 {UID: 单事件 ICS 文本}，errors 是解析不出来的清单。
    窗口以当前农历年为中心，往前 config.YEARS_BEFORE 年、往后 config.YEARS_AFTER 年，
    滚出窗口的旧事件在下次运行时被差集删除。

    UID = sha1(联系人UID | 公历日期 | 姓名 | SCHEMA)，四段各有用途：
    联系人 UID 保证改名不影响身份，公历日期保证每人每年一条，姓名保证改名后旧事件能被
    差集删掉，SCHEMA 是整个重建的开关。用哈希是为了不把姓名写进事件地址。
    """
    start = lunardate.LunarDate.from_solar_date(*date.today().timetuple()[:3]).year
    events, errors = {}, []
    for key, text in cards:
        try:
            v = vobject.readOne(text)
        except Exception as e:
            errors.append(err("E005", f"卡片 {key} 解析失败：{e}"))
            continue

        name = display_name(v)
        try:
            # 先把生日解析出来：没有农历标签的卡片直接跳过，缺名字也不算错
            items = list(lunar_birthdays(v, name or f"卡片 {key}"))
            if not items:
                continue
            if not name:
                raise BirthdayError(
                    "E013", f"卡片 {key}：有农历生日，但姓名和昵称都是空的，无法生成标题")
        except (BirthdayError, ValueError) as e:
            errors.append(str(e))
            continue

        pid = str(getattr(v, "uid", key).value if getattr(v, "uid", None) else key).strip()
        try:
            for month, day in items:
                for ly in range(start - config.YEARS_BEFORE, start + config.YEARS_AFTER + 1):
                    for solar, is_leap in lunar_dates(ly, month, day):
                        # 后缀 @lunar-birthday 是本程序写的事件的标记，our_events() 靠它
                        # 区分手工建的事件；末尾匹配，改动会让已有事件失去归属、再也不会被清理
                        uid = hashlib.sha1(
                            f"{pid}|{solar}|{name}|{SCHEMA}".encode()).hexdigest()[:20] + "@lunar-birthday"
                        title = f"{name}的生日" + (f"（闰{month}月）" if is_leap else "")

                        event = Event()
                        event.add("uid", uid)
                        # DTSTAMP 固定为事件当天，保证同样输入产出同样字节
                        event.add("dtstamp", datetime.combine(solar, time(0), tzinfo=timezone.utc))
                        event.add("dtstart", solar)                    # date 类型即全天事件
                        event.add("dtend", solar + timedelta(days=1))  # 全天事件要 DTEND 次日
                        event.add("summary", title)
                        event.add("transp", "TRANSPARENT")             # 不占用忙碌状态
                        # 不写 VALARM，提醒由用户在日历层面统一设置

                        cal = Calendar()
                        cal.add("prodid", "-//lunar-birthday//CN")
                        cal.add("version", "2.0")
                        cal.add_component(event)
                        events[uid] = cal.to_ical().decode()
        except (BirthdayError, ValueError) as e:
            errors.append(str(e))
    return events, errors


# ---- 日历同步 ----

def find_calendar(client, want):
    """按名称找目标日历，找不到就列出全部日历名后退出。

    Google 不支持用 CalDAV 建日历（MKCALENDAR 返回 404），必须手工建。
    """
    cals = client.principal().calendars()
    for cal in cals:
        if (cal.get_display_name() or "").strip() == want:
            return cal
    names = [(c.get_display_name() or "").strip() for c in cals]
    raise SystemExit(
        err("E004", f"没找到名为「{want}」的日历。先到 Google 日历左侧「其他日历」→ + → 创建新日历，"
                    f"名称填「{want}」。现有日历：{', '.join(n for n in names if n) or '（无）'}"))


def our_events(client, cal):
    """列出本程序写入的事件，返回 {UID: 事件地址}。

    只认 @lunar-birthday 后缀，手工建的事件不碰。用 PROPFIND 列目录而不是库的 events()，
    后者有时返回不完整。
    """
    body = XML + '<d:propfind xmlns:d="DAV:"><d:prop><d:getetag/></d:prop></d:propfind>'
    out = {}
    for e in kids(client.request(str(cal.url), "PROPFIND", body, PROPFIND).tree, "href"):
        name = urllib.parse.unquote(e.text.rstrip("/").rsplit("/", 1)[-1])  # @ 会被编码成 %40
        if name.endswith(".ics"):
            name = name[:-4]
        if name.endswith("@lunar-birthday"):
            out[name] = urllib.parse.urljoin(str(cal.url), e.text)
    return out


# 读回的事件里这些属性由服务端生成，值变了也不代表内容要重写，指纹比对时忽略。
# STATUS 是 Google 自动补的 CONFIRMED，空值属性（DESCRIPTION:、LOCATION:）也由它补，
# 所以 sig() 里把空值一并跳过，两边就对齐了。
VOLATILE = {"CREATED", "LAST-MODIFIED", "DTSTAMP", "SEQUENCE", "STATUS"}


def sig(text):
    """提取事件的内容指纹：全部属性（去掉服务端生成的、去掉空值、去掉子组件），排序后成元组。

    取全量而不是挑几项，是为了让「加一个字段」「改一行文案」这种结构变化自动被识别，
    不必靠人记得去动 SCHEMA。忽略 VOLATILE 是因为 Google 每次写入都会刷新它们，
    忽略 VALARM 是因为提醒可能在日历层面被改写，两者都不该触发重写。
    解析失败返回 None，调用方会因此选择重写，属于安全方向。
    """
    try:
        ev = [e for e in Calendar.from_ical(text).walk("VEVENT")][0]
    except Exception:
        return None
    props = []
    for key, value in ev.items():
        for item in (value if isinstance(value, list) else [value]):
            if isinstance(item, Component):
                continue
            prop = str(key).upper()
            if prop in VOLATILE or prop.startswith("X-"):
                continue
            if prop in ("DTSTART", "DTEND"):
                item = getattr(item, "dt", item)
                if isinstance(item, datetime):
                    item = item.date()  # date 与 datetime 直接比较永远不相等
            text_value = str(item).strip()
            if text_value:  # 空值属性由服务端补，不代表内容
                props.append((prop, text_value))
    return tuple(sorted(props))


# ---- 主流程 ----

def main():
    """读通讯录 → 算期望事件 → 与日历做差集 → 增删改 → 汇总。

    差集的做法决定了三种变更不需要单独写分支：期望集合每一项去日历集合里 pop 一次，
    pop 到即已存在、再比指纹；pop 不到即新建。循环结束后剩下的就是要删的。
    """
    email = os.environ.get("GCONTACTS_EMAIL", "").strip()
    pwd = os.environ.get("GCONTACTS_PASSWORD", "").replace(" ", "").strip()
    if not (email and pwd):
        sys.exit(err("E001", "缺 GCONTACTS_EMAIL / GCONTACTS_PASSWORD"))
    cal_name = config.CALENDAR_NAME

    created = updated = deleted = skipped = 0
    failed, events, notice = [], {}, ""

    try:
        with caldav.DAVClient(url=DAV_ROOT.format(urllib.parse.quote(email)),
                              username=email, password=pwd) as client:
            cards = fetch_cards(client, email)
            if not cards:
                # 空通讯录等于期望集合为空，差集会删光日历。认证通过但读不到东西时先拦住。
                sys.exit(err("E003", "通讯录返回 0 张卡片：多半是地址簿路径变了。"
                                     "为避免清空日历，本次不执行任何写入。"))
            events, errors = build_events(cards)
            cal = find_calendar(client, cal_name)
            existing = our_events(client, cal)
            failed = list(errors)

            for uid, ics in events.items():
                href = existing.pop(uid, None)
                try:
                    if href and sig(client.request(href, "GET").raw) == sig(ics):
                        skipped += 1
                        continue
                    # 更新用先删后建：Google 对已存在的条目 PUT 一律返回 409，
                    # 只接受 PUT 到不存在的路径。UID 不变，日历里仍是同一条。
                    target = href or (urllib.parse.quote(str(cal.url), safe=":/%")
                                      + urllib.parse.quote(uid, safe="") + ".ics")
                    if href:
                        r = client.request(href, "DELETE")
                        if r.status not in (200, 204, 404):
                            raise RuntimeError(f"HTTP {r.status}")
                    r = client.request(target, "PUT", ics.encode(),
                                       {"Content-Type": "text/calendar; charset=utf-8"})
                    if r.status not in (200, 201, 204):
                        raise RuntimeError(f"HTTP {r.status} {getattr(r, 'reason', '')}".strip())
                    if href:
                        updated += 1
                    else:
                        created += 1
                except Exception as e:
                    failed.append(err("E011", f"写入 {uid}：{e}"))

            # 解析出错时跳过删除：此时「算不出来」可能只是数据读不懂，不是用户删了联系人
            if errors:
                notice = f"有 {len(errors)} 处解析错误，本次跳过删除阶段，避免误删事件"
            else:
                for uid, href in existing.items():
                    try:
                        r = client.request(href, "DELETE")
                        if r.status not in (200, 204, 404):
                            raise RuntimeError(f"HTTP {r.status}")
                        deleted += 1
                    except Exception as e:
                        failed.append(err("E012", f"删除 {uid}：{e}"))
    except AuthorizationError:
        sys.exit(err("E002", "Google 认证失败：确认 GCONTACTS_EMAIL 是完整邮箱、"
                             "GCONTACTS_PASSWORD 是 16 位应用专用密码（不是登录密码）"))

    print(f"日历「{cal_name}」：新增 {created}，更新 {updated}，跳过 {skipped}，"
          f"删除 {deleted}，当前共 {len(events)} 个事件", flush=True)
    if notice:
        print(notice, file=sys.stderr)
    if failed:
        print(f"\n发现 {len(failed)} 处错误，需要人工修正：", file=sys.stderr)
        for line in failed:
            print("  - " + line, file=sys.stderr)
        used = sorted({c for c in (code_of(x) for x in failed) if c})
        print("错误码：" + "；".join(f"{c} {ERRORS[c]}" for c in used), file=sys.stderr)
        sys.exit(1)


if __name__ == "__main__":
    main()

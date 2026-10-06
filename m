#!/usr/bin/env python3
"""ankiterm - review Anki .apkg decks in the terminal (stdlib only).

usage:
  ankiterm.py deck.apkg              review interactively
  ankiterm.py deck.apkg -s           shuffled
  ankiterm.py deck.apkg -x out/      extract media (real names) + cards.txt
  ankiterm.py deck.apkg --dump       print every card as plain text
  ankiterm.py some_unzipped_dir/     also works on an already-unzipped folder
"""
import argparse, atexit, html, json, os, random, re, select, shutil
import sqlite3, subprocess, sys, tempfile, termios, tty, zipfile
from html.parser import HTMLParser

# ---------------------------------------------------------------- helpers

def zstd_decompress(data):
    try:
        import zstandard
        return zstandard.ZstdDecompressor().decompressobj().decompress(data)
    except ImportError:
        pass
    if shutil.which("zstd"):
        return subprocess.run(["zstd", "-dc"], input=data,
                              capture_output=True, check=True).stdout
    sys.exit("This deck uses Anki's newer compressed format; install zstd "
             "(app-arch/zstd) or the 'zstandard' Python module.")

def _varint(b, i):
    shift = val = 0
    while True:
        c = b[i]; i += 1
        val |= (c & 0x7F) << shift; shift += 7
        if not c & 0x80:
            return val, i

def pb_fields(buf):
    """Minimal protobuf decoder: {field_number: [values]}."""
    i, out = 0, {}
    while i < len(buf):
        key, i = _varint(buf, i)
        num, wt = key >> 3, key & 7
        if wt == 0:   val, i = _varint(buf, i)
        elif wt == 2: n, i = _varint(buf, i); val = buf[i:i + n]; i += n
        elif wt == 1: val = buf[i:i + 8]; i += 8
        elif wt == 5: val = buf[i:i + 4]; i += 4
        else: break
        out.setdefault(num, []).append(val)
    return out

# ---------------------------------------------------------------- loading

class Package:
    def __init__(self, path):
        if os.path.isdir(path):
            self.names = set(os.listdir(path))
            self._read = lambda n: open(os.path.join(path, n), "rb").read()
        else:
            z = zipfile.ZipFile(path)
            self.names = set(z.namelist())
            self._read = z.read

        self.version = 1
        if "meta" in self.names:
            self.version = pb_fields(self._read("meta")).get(1, [1])[0]

        for name in ("collection.anki21b", "collection.anki21", "collection.anki2"):
            if name in self.names:
                break
        else:
            sys.exit("No Anki collection found in that package.")
        data = self._read(name)
        if name.endswith("b"):
            data = zstd_decompress(data)
        tmp = tempfile.NamedTemporaryFile(suffix=".db", delete=False)
        tmp.write(data); tmp.close()
        atexit.register(os.unlink, tmp.name)
        self.db = sqlite3.connect(tmp.name)

        # media: zip member name -> real filename
        self.media = {}
        if "media" in self.names:
            raw = self._read("media")
            if self.version >= 3:
                for idx, entry in enumerate(pb_fields(zstd_decompress(raw)).get(1, [])):
                    self.media[str(idx)] = pb_fields(entry)[1][0].decode()
            elif raw.strip():
                self.media = json.loads(raw)
        self.by_name = {v: k for k, v in self.media.items()}

    def media_bytes(self, real_name):
        key = self.by_name.get(real_name)
        if key is None or key not in self.names:
            return None
        b = self._read(key)
        return zstd_decompress(b) if self.version >= 3 else b

    def notetypes_and_decks(self):
        db = self.db
        tables = {r[0] for r in db.execute(
            "select name from sqlite_master where type='table'")}
        models, decks = {}, {}
        row = db.execute("select models, decks from col").fetchone()
        if row and row[0] and row[0].strip() not in ("", "{}"):
            for mid, m in json.loads(row[0]).items():
                models[int(mid)] = {
                    "cloze": m.get("type") == 1,
                    "fields": [f["name"] for f in sorted(m["flds"], key=lambda f: f["ord"])],
                    "tmpls": {t["ord"]: (t["qfmt"], t["afmt"]) for t in m["tmpls"]},
                }
        if row and row[1] and row[1].strip() not in ("", "{}"):
            decks = {int(k): v["name"] for k, v in json.loads(row[1]).items()}
        if not models and "notetypes" in tables:          # newer schema
            for ntid, cfg in db.execute("select id, config from notetypes"):
                fields = [r[0] for r in db.execute(
                    "select name from fields where ntid=? order by ord", (ntid,))]
                tmpls = {}
                for o, tcfg in db.execute(
                        "select ord, config from templates where ntid=?", (ntid,)):
                    t = pb_fields(tcfg)
                    tmpls[o] = (t.get(1, [b""])[0].decode(), t.get(2, [b""])[0].decode())
                models[ntid] = {"cloze": pb_fields(cfg).get(1, [0])[0] == 1,
                                "fields": fields, "tmpls": tmpls}
        if not decks and "decks" in tables:
            decks = {i: n.replace("\x1f", "::")
                     for i, n in db.execute("select id, name from decks")}
        return models, decks

# ---------------------------------------------------------------- templates

CLOZE_RE = re.compile(r"\{\{c(\d+)::(.*?)(?:::(.*?))?\}\}", re.S)
HL_ON, HL_OFF = "\x01", "\x02"          # cloze highlight markers

def apply_cloze(text, n_target, side):
    def r(m):
        n, body, hint = int(m.group(1)), m.group(2), m.group(3)
        if n != n_target:
            return body
        return HL_ON + ("[" + (hint or "...") + "]" if side == "q" else body) + HL_OFF
    return CLOZE_RE.sub(r, text)

SECTION_RE = re.compile(r"\{\{([#^])\s*([^}]+?)\s*\}\}(.*?)\{\{/\s*\2\s*\}\}", re.S)
FIELD_RE = re.compile(r"\{\{(?![#^/!])([^}]+)\}\}")

def render(tmpl, fields, side, cloze_n, frontside=""):
    def has(name):
        return bool(re.sub(r"<[^>]+>|&nbsp;|\s", "", fields.get(name.strip(), "")))
    prev = None
    while prev != tmpl:
        prev = tmpl
        tmpl = SECTION_RE.sub(
            lambda m: m.group(3) if has(m.group(2)) != (m.group(1) == "^") else "", tmpl)

    def field(m):
        key = m.group(1).strip()
        if key == "FrontSide":
            return frontside
        *filters, name = key.split(":")
        val = fields.get(name.strip(), "")
        for f in reversed(filters):
            f = f.strip()
            if f == "cloze":      val = apply_cloze(val, cloze_n, side)
            elif f == "type":     val = "" if side == "q" else val
            elif f.startswith("tts"): val = ""
            elif f == "text":     val = re.sub(r"<[^>]+>", "", val)
        return val
    return FIELD_RE.sub(field, tmpl)

# ---------------------------------------------------------------- html -> terminal

ANSI = {"b": ("\x1b[1m", "\x1b[22m"), "i": ("\x1b[3m", "\x1b[23m"),
        "u": ("\x1b[4m", "\x1b[24m"), "code": ("\x1b[33m", "\x1b[39m"),
        "hl": ("\x1b[1;36m", "\x1b[22;39m")}
BLOCK = {"div", "p", "tr", "ul", "ol", "table", "blockquote", "section",
         "h1", "h2", "h3", "h4", "h5", "h6"}
STYLE = {"b": "b", "strong": "b", "i": "i", "em": "i", "u": "u"}

class ToText(HTMLParser):
    def __init__(self, color, width):
        super().__init__(convert_charrefs=True)
        self.color, self.width = color, width
        self.out, self.pre, self.skip = [], 0, 0

    def esc(self, kind, on):
        if self.color:
            self.out.append(ANSI[kind][0 if on else 1])

    def handle_starttag(self, tag, attrs):
        a = dict(attrs)
        if tag in ("style", "script"): self.skip += 1
        elif tag == "br":  self.out.append("\n")
        elif tag == "hr":  self.out.append("\n" + "─" * min(self.width, 60) + "\n")
        elif tag in BLOCK: self.out.append("\n")
        elif tag == "li":  self.out.append("\n  • ")
        elif tag in ("td", "th"): self.out.append("  ")
        elif tag == "pre": self.pre += 1; self.out.append("\n"); self.esc("code", True)
        elif tag == "code" and not self.pre: self.esc("code", True)
        elif tag in STYLE: self.esc(STYLE[tag], True)
        elif tag == "img": self.out.append(f"[image: {a.get('src', '')}]")

    def handle_endtag(self, tag):
        if tag in ("style", "script"): self.skip = max(0, self.skip - 1)
        elif tag in BLOCK or tag == "li": self.out.append("\n")
        elif tag == "pre":
            self.esc("code", False); self.pre = max(0, self.pre - 1); self.out.append("\n")
        elif tag == "code" and not self.pre: self.esc("code", False)
        elif tag in STYLE: self.esc(STYLE[tag], False)

    def handle_data(self, d):
        if self.skip:
            return
        if self.pre:
            d = d.replace("\t", "    ").replace(" ", "\xa0")
        else:
            d = re.sub(r"[ \t\r\n]+", " ", d)
        self.out.append(d)

def to_text(h, color=True, width=80):
    h = re.sub(r"\[sound:(.+?)\]", r"♪ \1", h)
    p = ToText(color, width); p.feed(h); p.close()
    s = "".join(p.out)
    s = s.replace(HL_ON, ANSI["hl"][0] if color else "").replace(HL_OFF, ANSI["hl"][1] if color else "")
    s = "\n".join(l.strip(" ").rstrip() for l in s.split("\n"))
    s = re.sub(r"\n{3,}", "\n\n", s).strip("\n").replace("\xa0", " ")
    return s + ("\x1b[0m" if color else "")

# ---------------------------------------------------------------- cards

class Card:
    __slots__ = ("deck", "tags", "q", "a", "back", "media")

def load_cards(pkg, deck_filter=None):
    models, decks = pkg.notetypes_and_decks()
    rows = pkg.db.execute(
        "select c.ord, c.did, n.mid, n.flds, n.tags from cards c "
        "join notes n on c.nid = n.id order by c.did, c.due, c.id").fetchall()
    cards = []
    for ord_, did, mid, flds, tags in rows:
        m = models.get(mid)
        if not m:
            continue
        deck = decks.get(did, "?")
        if deck_filter and deck_filter.lower() not in deck.lower():
            continue
        fields = dict(zip(m["fields"], flds.split("\x1f")))
        fields.update(Tags=tags.strip(), Deck=deck, Subdeck=deck.split("::")[-1])
        qf, af = m["tmpls"].get(0 if m["cloze"] else ord_, ("", ""))
        n = ord_ + 1
        c = Card()
        c.deck, c.tags = deck, tags.strip()
        c.q = render(qf, fields, "q", n)
        c.a = render(af, fields, "a", n, frontside=c.q)
        c.back = re.sub(r"^\s*<hr[^>]*>", "", render(af, fields, "a", n), flags=re.I)
        both = c.q + c.a
        c.media = list(dict.fromkeys(
            [html.unescape(s) for s in re.findall(r"""<img[^>]+src=["']?([^"'\s>]+)""", both, re.I)]
            + re.findall(r"\[sound:(.+?)\]", both)))
        cards.append(c)
    return cards

# ---------------------------------------------------------------- extract / dump

def dump_text(cards, color=False):
    out = []
    for i, c in enumerate(cards, 1):
        out.append(f"=== Card {i} — {c.deck}" + (f"  [{c.tags}]" if c.tags else ""))
        out.append(to_text(c.q, color))
        out.append("--- answer ---")
        out.append(to_text(c.back, color))
        out.append("")
    return "\n".join(out)

def extract(pkg, cards, outdir):
    os.makedirs(outdir, exist_ok=True)
    n = 0
    for name in pkg.media.values():
        data = pkg.media_bytes(name)
        if data is not None:
            with open(os.path.join(outdir, os.path.basename(name)), "wb") as f:
                f.write(data)
            n += 1
    with open(os.path.join(outdir, "cards.txt"), "w") as f:
        f.write(dump_text(cards))
    print(f"Wrote {n} media files and cards.txt ({len(cards)} cards) to {outdir}")

# ---------------------------------------------------------------- terminal UI

DIM, RST, REV = "\x1b[2m", "\x1b[0m", "\x1b[7m"

def getkey():
    fd = sys.stdin.fileno()
    old = termios.tcgetattr(fd)
    try:
        tty.setcbreak(fd)
        ch = os.read(fd, 1)
        if ch == b"\x1b":
            while select.select([fd], [], [], 0.03)[0]:
                ch += os.read(fd, 1)
    finally:
        termios.tcsetattr(fd, termios.TCSADRAIN, old)
    return ch.decode(errors="ignore")

def show(s):
    sys.stdout.write("\x1b[2J\x1b[H" + s); sys.stdout.flush()

HELP = """ankiterm keys

  space / enter   show answer, then next card ("good")
  a               on the answer: again (re-queue at the end)
  n  j  →         next card          p  k  ←   previous card
  f               flip front/back    s         shuffle remaining cards
  g               go to card number  l         view this card in less
  o               open the card's images/sounds
  ?               this help          q         quit

press any key"""

def open_media(pkg, card, tmpdir):
    if not card.media:
        return "no media on this card"
    w, h = shutil.get_terminal_size()
    for name in card.media:
        data = pkg.media_bytes(name)
        if data is None:
            continue
        path = os.path.join(tmpdir, os.path.basename(name))
        with open(path, "wb") as f:
            f.write(data)
        is_img = name.lower().rsplit(".", 1)[-1] in ("png", "jpg", "jpeg", "gif", "webp", "bmp", "svg")
        if is_img and shutil.which("chafa"):
            show(""); subprocess.run(["chafa", "-s", f"{w}x{h - 2}", path])
            print(f"\n{DIM}{name} — any key{RST}", end="", flush=True); getkey()
        elif not is_img and shutil.which("mpv"):
            subprocess.run(["mpv", "--really-quiet", path])
        elif shutil.which("xdg-open"):
            subprocess.Popen(["xdg-open", path], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        else:
            return f"saved to {path} (install chafa to view images here)"
    return ""

def review(pkg, cards, shuffle):
    queue = list(range(len(cards)))
    if shuffle:
        random.shuffle(queue)
    pos, back, again, msg = 0, False, 0, ""
    tmpdir = tempfile.mkdtemp(prefix="ankiterm-")
    atexit.register(shutil.rmtree, tmpdir, True)
    while True:
        w, h = shutil.get_terminal_size()
        if pos >= len(queue):
            show(f"\n  Done — {len(queue)} reviews, {again} marked again.\n\n"
                 f"  {DIM}r restart · p back · q quit{RST}")
            k = getkey()
            if k == "q": break
            if k == "r": pos, again = 0, 0; queue = queue[:len(cards)]
            if k in ("p", "k", "\x1b[D"): pos = len(queue) - 1
            continue
        c = cards[queue[pos]]
        body = to_text(c.a if back else c.q, True, w)
        head = f" {pos + 1}/{len(queue)}  {c.deck}" + (f"  [{c.tags}]" if c.tags else "")
        if back:
            keys = "space good · a again · n/p · o media · ? help · q quit"
        else:
            keys = "space answer · n/p · o media · ? help · q quit"
        if c.media: keys = f"{len(c.media)} media · " + keys
        if body.count("\n") > h - 6: keys = "l pager · " + keys
        show(f"{REV}{head[:w].ljust(w)}{RST}\n\n{body}\n\n{DIM}{keys}{RST}"
             + (f"\n{msg}" if msg else ""))
        msg = ""
        k = getkey()
        if k in ("q", "\x03"):
            break
        elif k in (" ", "\n", "\r"):
            if back: pos += 1; back = False
            else: back = True
        elif k == "a" and back:
            queue.append(queue[pos]); again += 1; pos += 1; back = False
        elif k in ("n", "j", "\x1b[C"): pos += 1; back = False
        elif k in ("p", "k", "\x1b[D"): pos = max(0, pos - 1); back = False
        elif k == "f": back = not back
        elif k == "s":
            rest = queue[pos + 1:]; random.shuffle(rest); queue[pos + 1:] = rest
            msg = "shuffled remaining cards"
        elif k == "g":
            try:
                pos = max(0, min(len(queue) - 1, int(input("\ngo to card #: ")) - 1)); back = False
            except ValueError:
                pass
        elif k == "l":
            subprocess.run(["less", "-R"], input=body.encode())
        elif k == "o":
            msg = open_media(pkg, c, tmpdir)
        elif k == "?":
            show(HELP); getkey()
    show("")

# ---------------------------------------------------------------- main

def main():
    ap = argparse.ArgumentParser(description="Review Anki .apkg decks in the terminal.")
    ap.add_argument("package", help=".apkg/.colpkg file, or a folder you already unzipped it into")
    ap.add_argument("-s", "--shuffle", action="store_true", help="shuffle card order")
    ap.add_argument("-d", "--deck", metavar="NAME", help="only cards whose deck name contains NAME")
    ap.add_argument("-x", "--extract", metavar="DIR", help="extract media with real names + cards.txt, then exit")
    ap.add_argument("--dump", action="store_true", help="print all cards as text and exit")
    args = ap.parse_args()

    pkg = Package(args.package)
    cards = load_cards(pkg, args.deck)
    if not cards:
        sys.exit("No cards found.")
    if args.extract:
        extract(pkg, cards, args.extract)
    elif args.dump or not sys.stdin.isatty():
        print(dump_text(cards, color=sys.stdout.isatty()))
    else:
        try:
            review(pkg, cards, args.shuffle)
        except KeyboardInterrupt:
            show("")

if __name__ == "__main__":
    main()

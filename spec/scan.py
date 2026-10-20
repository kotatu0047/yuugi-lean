#!/usr/bin/env python3
"""CardGen のソースに、検査をすり抜ける書き方がないかを調べる（コメントと文字列は除く）。

公理の検査（spec/Spec/Check.lean）は検査した定理が依存するものしか見ないので、ここでは CardGen 全体を見る。
見つかれば終了コード 1。
"""
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
FORBIDDEN = {
    r"\bsorry\b": "sorry",
    r"\badmit\b": "admit",
    r"\bnative_decide\b": "native_decide",
    r"\bdecide\s*\+\s*native\b": "decide +native",
    r"(?m)^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+)?axiom\b": "axiom",
    r"\bunsafe\b": "unsafe",
    r"\bimplemented_by\b": "implemented_by",
    r"@\[\s*extern\b": "extern",
    r"\bdebug\.skipKernelTC\b": "debug.skipKernelTC",
    r"\bLean\.ofReduceBool\b": "ofReduceBool",
    r"#exit\b": "#exit",
}


def strip(src: str) -> str:
    """コメント（入れ子の /- -/ と --）と文字列を空白に置き換える。行番号は保つ"""
    out, i, n, depth = [], 0, len(src), 0
    while i < n:
        if depth == 0 and src.startswith("--", i):
            j = src.find("\n", i)
            j = n if j < 0 else j
            out.append(" " * (j - i)); i = j
        elif src.startswith("/-", i):
            depth += 1; out.append("  "); i += 2
        elif depth > 0 and src.startswith("-/", i):
            depth -= 1; out.append("  "); i += 2
        elif depth > 0:
            out.append("\n" if src[i] == "\n" else " "); i += 1
        elif src[i] == '"':
            j = i + 1
            while j < n and src[j] != '"':
                j += 2 if src[j] == "\\" else 1
            out.append("".join("\n" if c == "\n" else " " for c in src[i:j + 1])); i = j + 1
        elif src.startswith("'\"'", i):
            out.append("   "); i += 3
        else:
            out.append(src[i]); i += 1
    return "".join(out)


bad = []
files = sorted((ROOT / "CardGen").rglob("*.lean")) + [ROOT / "CardGen.lean"]
for f in files:
    code = strip(f.read_text())
    for pat, name in FORBIDDEN.items():
        for m in re.finditer(pat, code):
            line = code.count("\n", 0, m.start()) + 1
            bad.append(f"{f.relative_to(ROOT)}:{line}: {name}")
if bad:
    print("検査をすり抜ける書き方があります：", file=sys.stderr)
    print("\n".join("  " + b for b in bad), file=sys.stderr)
    sys.exit(1)
print(f"CardGen のソース {len(files)} 個に、禁止した書き方はない")

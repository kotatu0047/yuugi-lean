#!/usr/bin/env python3
"""レポートが「証明済み」として名前を出す定理が、どれも spec/Spec/Check.lean で検査されているかを確かめる。

名前は2か所から集める：CardGen/Report.lean のソースの文字列と、見本のゲームでの検査ツールの実際の出力。
検査されていない名前があれば、終了コード 1。
"""
import json
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
NAME = r"CardGen\.[A-Za-z_][A-Za-z0-9_?]*(?:\.[A-Za-z_][A-Za-z0-9_?]*)*"

checked = set(re.findall(r"@(" + NAME + r")", (ROOT / "spec/Spec/Check.lean").read_text()))

cited = set(re.findall(r"[\"：](" + NAME + r")", (ROOT / "CardGen/Report.lean").read_text()))


def strings(x):
    if isinstance(x, str):
        yield x
    elif isinstance(x, dict):
        for v in x.values():
            yield from strings(v)
    elif isinstance(x, list):
        for v in x:
            yield from strings(v)


for game in ["CardGen/sample.json", "CardGen/mtg.json"]:
    out = subprocess.run(["lake", "exe", "cardgen", game], cwd=ROOT, capture_output=True, text=True, check=True).stdout
    for s in strings(json.loads(out)):
        cited.update(re.findall(NAME, s))

missing = sorted(cited - checked)
if missing:
    print("spec/Spec/Check.lean で検査していない定理を、レポートが名前で出しています：", file=sys.stderr)
    for n in missing:
        print("  " + n, file=sys.stderr)
    sys.exit(1)
print(f"レポートが名前を出す定理 {len(cited)} 本は、どれも凍結した主張と照合済み")

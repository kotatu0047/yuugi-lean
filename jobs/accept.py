#!/usr/bin/env python3
"""証明のジョブを機械的に検査して受け入れる。

    python3 jobs/accept.py jobs/pending/0001
    python3 jobs/accept.py --recheck      # 受け入れ済みのジョブを今のライブラリでもう一度検査する

1. job.json の頭の部分（JobStatement までの定義。変えてはいけない）と、証明する側が書いた
   Proof.lean と、確認の部分をつなげて1つの Lean ファイルにする
2. Proof.lean に、検査をすり抜ける書き方（sorry・axiom・カーネルの検査を飛ばす設定など）がないか調べる
3. lake env lean でコンパイルし、エラーがないこと、`example : JobStatement := job_proof` が通ること
   （= 証明した文が JobStatement そのもの）、job_proof が使う公理が Lean 標準のものだけであることを確かめる
4. 受け入れたら、つなげたファイルを Job.lean として保存し、jobs/done/ へ移す。
   受け入れなければ、理由を result.json に書いて jobs/pending/ に残す

証明する側が誰（Claude・ローカルのモデル・人）でも、この検査は同じ。
"""
import datetime
import json
import pathlib
import re
import shutil
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
FORBIDDEN = [
    (r"\bsorry\b", "sorry"),
    (r"\badmit\b", "admit"),
    (r"\baxiom\b", "axiom の宣言"),
    (r"\bunsafe\b", "unsafe"),
    (r"implemented_by|@\[extern", "実装の差し替え"),
    (r"native_decide|ofReduceBool|ofReduceNat", "native_decide（コンパイラを信頼する公理）"),
    (r"debug\.skipKernelTC|set_option\s+debug", "カーネルの検査を変える設定"),
    (r"#exit|^\s*end\s+Job_", "ファイルの構造を変える書き方"),
    (r"^\s*import\b", "import の追加"),
]


def check(job_dir: pathlib.Path) -> dict:
    job = json.loads((job_dir / "job.json").read_text(encoding="utf-8"))
    proof = (job_dir / "Proof.lean").read_text(encoding="utf-8")
    jid = job["id"]
    problems = [f"Proof.lean に {name} があります" for pat, name in FORBIDDEN if re.search(pat, proof, re.M)]
    if problems:
        return {"status": "rejected", "reasons": problems}

    footer = f"""
-- 受け入れの確認：証明したのは JobStatement そのもの
example : JobStatement := job_proof
#print axioms job_proof

end Job_{jid}
"""
    source = job["header"] + proof + footer
    check_dir = ROOT / "jobs" / ".check"
    check_dir.mkdir(exist_ok=True)
    path = check_dir / f"Job_{jid}.lean"
    path.write_text(source, encoding="utf-8")
    r = subprocess.run(["lake", "env", "lean", str(path)], cwd=ROOT, capture_output=True, text=True, timeout=1800)
    out = r.stdout + r.stderr
    errors = [l for l in out.splitlines() if ": error" in l]
    if r.returncode != 0 or errors:
        return {"status": "rejected", "reasons": ["コンパイルできません"] + errors[:20], "output": out[-4000:]}
    m = re.search(r"depends on axioms: \[(.*?)\]", out)
    axioms = [a.strip() for a in m.group(1).split(",")] if m else []
    extra = [a for a in axioms if a not in ALLOWED_AXIOMS]
    if extra:
        return {"status": "rejected", "reasons": [f"使ってはいけない公理：{', '.join(extra)}"]}
    if "declaration uses 'sorry'" in out:
        return {"status": "rejected", "reasons": ["sorry が使われています"]}
    return {"status": "accepted", "axioms": axioms, "source": source}


def recheck() -> int:
    """受け入れ済みのジョブを、今のライブラリでもう一度検査する（定義を変えたあとに使う）"""
    broken = []
    for job_dir in sorted((ROOT / "jobs" / "done").iterdir()):
        if not (job_dir / "job.json").exists():
            continue
        result = check(job_dir)
        ok = result["status"] == "accepted"
        print(f"{job_dir.name}: {'通る' if ok else '通らない'}")
        if not ok:
            broken.append(job_dir.name)
            for reason in result["reasons"][:5]:
                print("    " + reason)
    if broken:
        print("通らなくなったジョブは jobs/pending/ に戻して証明を直す：" + "、".join(broken))
        return 1
    return 0


def main() -> int:
    if sys.argv[1:] == ["--recheck"]:
        return recheck()
    job_dir = pathlib.Path(sys.argv[1]).resolve()
    result = check(job_dir)
    result["checkedAt"] = datetime.datetime.now().astimezone().isoformat(timespec="seconds")
    source = result.pop("source", None)
    (job_dir / "result.json").write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    if result["status"] == "accepted":
        (job_dir / "Job.lean").write_text(source, encoding="utf-8")
        dest = ROOT / "jobs" / "done" / job_dir.name
        shutil.move(str(job_dir), str(dest))
        print(f"受け入れました：{dest}")
        return 0
    print("受け入れませんでした：")
    for reason in result["reasons"]:
        print("  " + reason)
    return 1


if __name__ == "__main__":
    sys.exit(main())

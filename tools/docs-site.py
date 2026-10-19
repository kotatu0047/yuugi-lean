#!/usr/bin/env python3
"""リポジトリのドキュメント（Markdown）を、Web 用のサイト（MkDocs）の入力に集める。

    python3 tools/docs-site.py        # _docs_site/ に写す（mkdocs build がここを読む）

本文の中の `企画書.md` のようなファイル名は、サイトのページへのリンクに変える。
"""
import pathlib
import re
import shutil

ROOT = pathlib.Path(__file__).resolve().parent.parent
OUT = ROOT / "_docs_site"

# リポジトリのファイル → サイトのページ
PAGES = {
    "README.md": "index.md",
    "企画書.md": "企画書.md",
    "アーキテクチャ.md": "アーキテクチャ.md",
    "CardGen/中間表現.md": "中間表現.md",
    "jobs/README.md": "ジョブ.md",
    "csharp/README.md": "csharp.md",
    "unity/CardGenEditor/README.md": "unity.md",
    "4すくみ考察.md": "4すくみ考察.md",
    "会話記録.md": "会話記録.md",
}

# 本文での書き方 → リンク先（バッククォートで囲んだファイル名をリンクにする）
NAMES = {src: dst for src, dst in PAGES.items()}
NAMES.update({src.split("/")[-1]: dst for src, dst in PAGES.items() if src.count("/") == 1 and not src.endswith("README.md")})


def link(text: str) -> str:
    def repl(m):
        name = m.group(1)
        dst = NAMES.get(name)
        return f"[`{name}`]({dst})" if dst else m.group(0)
    # すでにリンクの中にあるものと、コードブロックの中は変えない
    out, in_code = [], False
    for line in text.split("\n"):
        if line.startswith("```"):
            in_code = not in_code
        out.append(line if in_code else re.sub(r"(?<!\[)`([^`\n]+\.md)`(?!\])", repl, line))
    return "\n".join(out)


def main():
    if OUT.exists():
        shutil.rmtree(OUT)
    OUT.mkdir()
    for src, dst in PAGES.items():
        (OUT / dst).write_text(link((ROOT / src).read_text(encoding="utf-8")), encoding="utf-8")
    # サイト用の JavaScript と CSS（mermaid の図の全画面表示）
    shutil.copytree(ROOT / "docs-assets", OUT / "assets" / "extra")
    print(f"{len(PAGES)} ページを {OUT} に写しました")


if __name__ == "__main__":
    main()

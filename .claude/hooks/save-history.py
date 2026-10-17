#!/usr/bin/env python3
"""Claude Code の会話を .claude-history/ に Markdown で保存するフック。

- Stop（応答のたび）: Markdown を書き直すだけ
- SessionEnd（セッション終了時）: 書き直したうえで、そのファイルだけをコミットする（push はしない）

ユーザーとアシスタントの本文だけを残す。ツールの実行結果・思考・システムからの注入・
サブエージェントの会話は含めず、トークンらしい文字列は伏せ字にする。
"""
import json
import os
import re
import subprocess
import sys
from datetime import datetime

SECRET_PATTERNS = [
    (re.compile(r"(github_pat_|gh[pousr]_)[A-Za-z0-9_]{8,}"), r"\1***"),
    (re.compile(r"sk-ant-[A-Za-z0-9_\-]{8,}"), "sk-ant-***"),
    (re.compile(r"sk-[A-Za-z0-9]{20,}"), "sk-***"),
    (re.compile(r"AKIA[0-9A-Z]{16}"), "AKIA***"),
]
PASTED_TAG = re.compile(r"</?pasted_content[^>]*>")
BASH_TAG = re.compile(r"<(bash-input|bash-stdout|bash-stderr)>(.*?)</\1>", re.S)


def redact(text: str) -> str:
    for pat, rep in SECRET_PATTERNS:
        text = pat.sub(rep, text)
    return text


def local_time(ts: str) -> str:
    try:
        return datetime.fromisoformat(ts.replace("Z", "+00:00")).astimezone().strftime("%Y-%m-%d %H:%M")
    except (ValueError, AttributeError):
        return ""


def render_user(text: str) -> str:
    text = PASTED_TAG.sub("", text).strip()

    def bash(m):
        body = m.group(2).strip()
        if not body:
            return ""
        prefix = "$ " if m.group(1) == "bash-input" else ""
        return f"\n```\n{prefix}{body}\n```\n"

    return BASH_TAG.sub(bash, text).strip()


def build(transcript: str) -> tuple[str, str]:
    """(Markdown 本文, 最初の日付) を返す"""
    blocks: list[tuple[str, str, str]] = []  # (role, time, text)
    first = ""
    for line in open(transcript, encoding="utf-8"):
        try:
            d = json.loads(line)
        except json.JSONDecodeError:
            continue
        kind = d.get("type")
        if kind not in ("user", "assistant") or d.get("isSidechain") or d.get("isMeta"):
            continue
        content = (d.get("message") or {}).get("content")
        ts = d.get("timestamp", "")
        first = first or ts
        if kind == "user":
            if d.get("isCompactSummary") and isinstance(content, str):
                blocks.append(("summary", local_time(ts), content.strip()))
                continue
            if isinstance(content, str):
                text = render_user(content)
            elif isinstance(content, list):
                # tool_result は含めない。中断の通知などの文字列だけを拾う
                text = "\n".join(c.get("text", "") for c in content if c.get("type") == "text").strip()
                if text.startswith("[Request interrupted"):
                    text = "*（中断）*"
            else:
                text = ""
            if text:
                blocks.append(("user", local_time(ts), text))
        else:
            if not isinstance(content, list):
                continue
            text = "\n".join(c.get("text", "") for c in content if c.get("type") == "text").strip()
            if not text:
                continue
            # 同じ応答の中で分かれた本文はまとめる
            if blocks and blocks[-1][0] == "assistant":
                role, t, prev = blocks[-1]
                blocks[-1] = (role, t, prev + "\n\n" + text)
            else:
                blocks.append(("assistant", local_time(ts), text))

    out = []
    for role, t, text in blocks:
        text = redact(text)
        if role == "summary":
            out.append(f"<details><summary>文脈の要約（{t}）</summary>\n\n{text}\n\n</details>\n")
        else:
            name = "ユーザー" if role == "user" else "Claude"
            out.append(f"## {name}（{t}）\n\n{text}\n")
    return "\n".join(out), local_time(first)[:10]


def git(*args: str, cwd: str) -> subprocess.CompletedProcess:
    return subprocess.run(["git", *args], cwd=cwd, capture_output=True, text=True, timeout=60)


def main() -> None:
    data = json.load(sys.stdin)
    transcript = data.get("transcript_path")
    session = data.get("session_id", "unknown")
    event = data.get("hook_event_name", "")
    project = os.environ.get("CLAUDE_PROJECT_DIR") or data.get("cwd") or os.getcwd()
    if not transcript or not os.path.exists(transcript):
        return

    body, day = build(transcript)
    if not body:
        return
    dest = os.path.join(project, ".claude-history")
    os.makedirs(dest, exist_ok=True)
    name = f"{day or 'unknown'}_{session[:8]}.md"
    path = os.path.join(dest, name)
    new = f"# 会話ログ {day}（セッション {session[:8]}）\n\n" + body
    old = open(path, encoding="utf-8").read() if os.path.exists(path) else None
    if new != old:
        with open(path, "w", encoding="utf-8") as f:
            f.write(new)

    if event != "SessionEnd":
        return
    rel = os.path.join(".claude-history", name)
    git("add", "--", rel, cwd=project)
    if git("diff", "--cached", "--quiet", "--", rel, cwd=project).returncode != 0:
        git("commit", "-m", f"会話ログを保存（{day} セッション {session[:8]}）", "--", rel, cwd=project)


if __name__ == "__main__":
    try:
        main()
    except Exception as e:  # フックの失敗で Claude Code を止めない
        print(f"save-history: {e}", file=sys.stderr)

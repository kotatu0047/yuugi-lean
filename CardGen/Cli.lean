import CardGen.Report
import CardGen.Vectors

/-!
# 検査ツール

```
lake exe cardgen ファイル.json          # JSON で報告（Unity などから読む）
lake exe cardgen ファイル.json --text   # 人が読む形で報告
lake exe cardgen - < ファイル.json      # 標準入力から読む
lake exe cardgen --vectors 出力.json   # C# との差分テスト用のテストベクトルを書き出す
```

形式の誤りがあれば終了コード 1、なければ 0。
-/

open CardGen Lean

def main (args : List String) : IO UInt32 := do
  if let "--vectors" :: out :: _ := args then
    IO.FS.writeFile out (vectors.pretty ++ "\n")
    return 0
  let text := args.contains "--text"
  let path := (args.filter (· != "--text")).headD "-"
  let input ← if path == "-" then (← IO.getStdin).readToEnd else IO.FS.readFile path
  let r := report input
  IO.println (if text then r.toText else (toJson r).pretty)
  return if r.ok then 0 else 1

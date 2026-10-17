import CardGen.Report
import CardGen.Vectors
import CardGen.Custom

/-!
# 検査ツール

```
lake exe cardgen ファイル.json          # JSON で報告（Unity などから読む）
lake exe cardgen ファイル.json --text   # 人が読む形で報告
lake exe cardgen - < ファイル.json      # 標準入力から読む
lake exe cardgen --vectors 出力.json   # C# との差分テスト用のテストベクトルを書き出す
lake exe cardgen --job ゲーム.json 命題.json [jobs]   # 追加した命題の反例を探し、なければ証明のジョブを書き出す
```

形式の誤りがあれば終了コード 1、なければ 0。
-/

open CardGen Lean

/-- ジョブの番号：`jobs/pending` と `jobs/done` にある番号の次 -/
def nextJobId (dir : System.FilePath) : IO String := do
  let mut m := 0
  for sub in ["pending", "done"] do
    let d := dir / sub
    if ← d.isDir then
      for e in ← d.readDir do
        if let some n := e.fileName.toNat? then m := max m n
  let s := toString (m + 1)
  return String.ofList (List.replicate (4 - s.length) (Char.ofNat 48)) ++ s

def makeJob (gamePath claimPath : String) (dir : System.FilePath) : IO UInt32 := do
  let g ← IO.ofExcept (Game.parse (← IO.FS.readFile gamePath))
  let c ← IO.ofExcept ((Json.parse (← IO.FS.readFile claimPath)).bind fromJson? : Except String CustomClaim)
  match c.findCounterexample g.rules g.cards with
  | some ce =>
    let chs := ce.choices.map fun
      | .draw p => json% {kind: "draw", player: $(p)}
      | .place p h z up => json% {kind: "place", player: $(p), hand: $(h), zone: $(z), faceUp: $(up)}
      | .resolve p k e a => json% {kind: "resolve", player: $(p), field: $(k), effect: $(e), apply: $(a)}
    IO.println (json% {status: "counterexample", title: $(c.title), count: $(ce.count), decks: $(ce.decks),
      choices: $(chs)}).pretty
    return 1
  | none =>
    let id ← nextJobId dir
    let jd := dir / "pending" / id
    IO.FS.createDirAll jd
    IO.FS.writeFile (jd / "job.json") ((c.jobJson g id).pretty ++ "\n")
    IO.FS.writeFile (jd / "Proof.lean") jobProofTemplate
    IO.println (json% {status: "queued", id: $(id), path: $(jd.toString)}).pretty
    return 0

def main (args : List String) : IO UInt32 := do
  if let "--vectors" :: out :: _ := args then
    IO.FS.writeFile out (vectors.pretty ++ "\n")
    return 0
  if let "--job" :: gamePath :: claimPath :: rest := args then
    return ← makeJob gamePath claimPath (rest.headD "jobs")
  let text := args.contains "--text"
  let path := (args.filter (· != "--text")).headD "-"
  let input ← if path == "-" then (← IO.getStdin).readToEnd else IO.FS.readFile path
  let r := report input
  IO.println (if text then r.toText else (toJson r).pretty)
  return if r.ok then 0 else 1

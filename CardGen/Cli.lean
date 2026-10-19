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
lake exe cardgen --job-stdin [jobs]    # 同じことを、標準入力の {"game": …, "claim": …} で行う（Unity から使う）
lake exe cardgen --jobs [jobs]         # ジョブの一覧と状態
```

ジョブのフォルダを省くと、検査ツールのあるリポジトリの `jobs`（`リポジトリ/.lake/build/bin/cardgen` から見て）。
形式の誤りがある・反例が見つかったときは終了コード 1、それ以外は 0。
-/

open CardGen Lean

/-- リポジトリの jobs フォルダ（検査ツールは リポジトリ/.lake/build/bin/cardgen にある） -/
def defaultJobsDir : IO System.FilePath := do
  let app ← IO.appPath
  match app.parent.bind (·.parent) |>.bind (·.parent) |>.bind (·.parent) with
  | some root => return root / "jobs"
  | none => return "jobs"

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

/-- 反例を探し、なければジョブを書き出す -/
def makeJobFrom (g : Game) (c : CustomClaim) (dir : System.FilePath) : IO UInt32 := do
  match c.findCounterexample g.rules g.cards with
  | some ce =>
    IO.println (json% {status: "counterexample", title: $(c.title), count: $(ce.count), decks: $(ce.decks),
      choices: $(ce.choices.map choiceJson)}).pretty
    return 1
  | none =>
    let id ← nextJobId dir
    let jd := dir / "pending" / id
    IO.FS.createDirAll jd
    IO.FS.writeFile (jd / "job.json") ((c.jobJson g id).pretty ++ "\n")
    IO.FS.writeFile (jd / "Proof.lean") jobProofTemplate
    IO.println (json% {status: "queued", id: $(id), path: $(jd.toString)}).pretty
    return 0

def parseClaim (j : Json) : Except String CustomClaim := fromJson? j

/-- ジョブの一覧と状態（pending / accepted / rejected） -/
def listJobs (dir : System.FilePath) : IO Json := do
  let mut out : Array Json := #[]
  for sub in ["pending", "done"] do
    let d := dir / sub
    if !(← d.isDir) then continue
    let entries := (← d.readDir).qsort (·.fileName < ·.fileName)
    for e in entries do
      if !(← (e.path / "job.json").pathExists) then continue
      let job ← IO.ofExcept (Json.parse (← IO.FS.readFile (e.path / "job.json")))
      let title := (job.getObjValAs? String "title").toOption.getD ""
      let res ← if ← (e.path / "result.json").pathExists then
          pure (Json.parse (← IO.FS.readFile (e.path / "result.json"))).toOption else pure none
      let status := (res.bind fun r => (r.getObjValAs? String "status").toOption).getD "pending"
      let reasons := (res.bind fun r => (r.getObjValAs? (List String) "reasons").toOption).getD []
      out := out.push (json% {id: $(e.fileName), title: $(title), status: $(status), reasons: $(reasons)})
  return toJson out

def jobsDirArg (rest : List String) : IO System.FilePath :=
  match rest with
  | d :: _ => pure d
  | [] => defaultJobsDir

def jobStdin (rest : List String) : IO UInt32 := do
  let j ← IO.ofExcept (Json.parse (← (← IO.getStdin).readToEnd))
  let g ← IO.ofExcept ((j.getObjVal? "game").bind fun gj => (fromJson? gj : Except String Game))
  let es := g.check
  if !es.isEmpty then
    IO.println (json% {status: "error", errors: $(es)}).pretty
    return 1
  let c ← IO.ofExcept ((j.getObjVal? "claim").bind parseClaim)
  makeJobFrom g c (← jobsDirArg rest)

def main (args : List String) : IO UInt32 := do
  match args with
  | "--vectors" :: out :: _ =>
    IO.FS.writeFile out ((vectors ()).pretty ++ "\n")
    return 0
  | "--job" :: gamePath :: claimPath :: rest =>
    let g ← IO.ofExcept (Game.parse (← IO.FS.readFile gamePath))
    let c ← IO.ofExcept ((Json.parse (← IO.FS.readFile claimPath)).bind parseClaim)
    makeJobFrom g c (← jobsDirArg rest)
  | "--job-stdin" :: rest => jobStdin rest
  | "--game-vectors" :: path :: rest =>
    -- ユーザーのゲームのテストベクトル（path が - なら標準入力から読む）。続けて対戦の数と手数を指定できる
    let input ← if path == "-" then (← IO.getStdin).readToEnd else IO.FS.readFile path
    let g ← IO.ofExcept ((Json.parse input).bind fun j => (fromJson? j : Except String Game))
    let games := (rest.head?.bind String.toNat?).getD 12
    let steps := (rest[1]?.bind String.toNat?).getD 80
    IO.println (gameVectors g games steps).compress
    return 0
  | "--jobs" :: rest =>
    IO.println (← listJobs (← jobsDirArg rest)).pretty
    return 0
  | _ =>
    let text := args.contains "--text"
    let path := (args.filter (· != "--text")).headD "-"
    let input ← if path == "-" then (← IO.getStdin).readToEnd else IO.FS.readFile path
    let r := report input
    IO.println (if text then r.toText else (toJson r).pretty)
    return if r.ok then 0 else 1

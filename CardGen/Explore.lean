import CardGen.Negation

/-!
# 循環があるときの総当たりの検査（第3層）

無効にしうる関係に循環があるカードのまとまりについて、小さな盤面をすべて作り、
判定の手続き（`System.Step`、順番を自由にした反転）の振る舞いを調べる。盤面の作り方と、
OCG の手順（適用の時刻つき）での判定は `Timed.lean`。

盤面ごとに、次のどれかに分類する（下ほど悪い）。

| 分類 | 意味 | 報告の状態 |
|---|---|---|
| `ok` | どの状態からどう選んでも止まり、安定な状態は1つ | — |
| `someLoop` | 安定な状態は1つだが、選び方によって回り続ける | プレイヤーの選択 |
| `multiStable` | 安定な状態が複数あり、結果が順番で変わる | プレイヤーの選択 |
| `cannotHalt` | どう選んでも止まらない状態がある | 反例あり |
| `noStable` | 安定な状態がない（どう選んでも止まらない） | 反例あり |

これは計算による検査で、調べた盤面についての結果である。
-/

namespace CardGen

inductive Verdict
  | ok | someLoop | multiStable | cannotHalt | noStable
deriving Repr, DecidableEq

def Verdict.severity : Verdict → Nat
  | .ok => 0 | .someLoop => 1 | .multiStable => 2 | .cannotHalt => 3 | .noStable => 4

/-- 盤面の判定の手続きを、すべての状態（`2^n` 通り）について調べる -/
def analyzeBoard (insts : List Inst) : Verdict := Id.run do
  let n := insts.length
  let N := 2 ^ n
  let rel : Array (Array Bool) := (List.range n).toArray.map fun y =>
    (List.range n).toArray.map fun x => instRel insts y x
  let bit (s x : Nat) : Bool := (s >>> x) % 2 == 1
  let negated (s x : Nat) : Bool := (List.range n).any fun y => (rel[y]!)[x]! && bit s y
  let succ (s : Nat) : List Nat :=
    (List.range n).filterMap fun x => if bit s x == negated s x then some (s ^^^ (1 <<< x)) else none
  let succs : Array (List Nat) := (List.range N).toArray.map succ
  let halting : Array Bool := succs.map (·.isEmpty)
  let stables := (halting.toList.filter id).length
  if stables == 0 then return .noStable
  -- どこかで止まれる状態
  let mut canHalt := halting
  let mut changed := true
  while changed do
    changed := false
    for s in [0:N] do
      if !canHalt[s]! && (succs[s]!).any (canHalt[·]!) then
        canHalt := canHalt.set! s true
        changed := true
  if canHalt.any (!·) then return .cannotHalt
  if stables > 1 then return .multiStable
  -- どう選んでも止まる状態
  let mut allHalt := halting
  changed := true
  while changed do
    changed := false
    for s in [0:N] do
      if !allHalt[s]! && (succs[s]!).all (allHalt[·]!) then
        allHalt := allHalt.set! s true
        changed := true
  if allHalt.any (!·) then return .someLoop
  return .ok

end CardGen

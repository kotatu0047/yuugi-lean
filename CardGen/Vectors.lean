import CardGen.Sample
import CardGen.Play

/-!
# 差分テスト用のテストベクトル

C# のゲームエンジンが Lean の定義と同じ結果を出すかを確かめるための、入力と期待する出力の組。
`lake exe cardgen --vectors ファイル.json` で書き出す。乱数は固定の種から作るので、毎回同じ内容になる。

- `selector`：範囲の指定（`Selector.matches`）
- `check`：形式の検査（`Game.check`）。誤りの文章も一致させる
- `destroy`：破壊の動き（`PState.destroy`）
- `boards`：盤面の無効の関係（`instRel`）と判定の手続きの分類（`analyzeBoard`）
- `play`：小さなルール（`playRules`）での対戦。開始時の状態から、選んだ動きを `State.step?` で進める
  （できない動きは `null`）

カードは `cards` の名前で参照する。
-/

namespace CardGen
open Lean

/-- 線形合同法の乱数 -/
abbrev Rand := StateM Nat

def Rand.next (k : Nat) : Rand Nat := do
  let s ← get
  let s' := (s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64
  set s'
  return (s' >>> 33) % k

def Rand.bool : Rand Bool := return (← Rand.next 2) == 1

def Rand.pick {α} [Inhabited α] (l : List α) : Rand α := return l[← Rand.next l.length]!

def Rand.subset {α} (l : List α) : Rand (List α) := l.filterM fun _ => Rand.bool

def Rand.list {α} (n : Nat) (m : Rand α) : Rand (List α) := (List.range n).mapM fun _ => m

instance : Inhabited Card := ⟨⟨"", "", [], []⟩⟩
instance : Inhabited Side := ⟨.both⟩

def vecTypes : List TypeName := ["モンスター", "魔法", "罠"]
def vecTags : List String := ["闇属性", "機械族", "戦士族"]

def Rand.selector : Rand Selector := do
  let ts ← Rand.subset vecTypes
  let types ← if ts.isEmpty then (do return [← Rand.pick vecTypes]) else pure ts
  return { types, tags := ← Rand.subset vecTags, side := ← Rand.pick [.self, .opp, .both],
           faceUpOnly := ← Rand.bool, excludeSelf := ← Rand.bool }

def Rand.view : Rand View := do
  return { type := ← Rand.pick vecTypes, tags := ← Rand.subset vecTags, mine := ← Rand.bool,
           faceUp := ← Rand.bool, isSelf := ← Rand.bool }

def viewJson (v : View) : Json :=
  json% {type: $(v.type), tags: $(v.tags), mine: $(v.mine), faceUp: $(v.faceUp), isSelf: $(v.isSelf)}

def slotJson (sl : Slot) : Json := json% {zone: $(sl.zone), card: $(sl.card.name), faceUp: $(sl.faceUp)}

def pstateJson (s : PState) : Json :=
  json% {deck: $(s.deck.map (·.name)), hand: $(s.hand.map (·.name)), grave: $(s.grave.map (·.name)),
         field: $(s.field.map slotJson)}

def instJson (i : Inst) : Json := json% {card: $(i.card.name), controller: $(i.controller), faceUp: $(i.faceUp)}

def verdictName : Verdict → String
  | .ok => "ok" | .someLoop => "someLoop" | .multiStable => "multiStable"
  | .cannotHalt => "cannotHalt" | .noStable => "noStable"

/-- テストに使うカード：見本の8枚と、循環のない例・自分を無効にする例 -/
def vecCards : List Card := Sample.game.cards ++ [Sample.spellBreaker, Sample.selfNegator]

/-- 形式の検査のテスト：見本と、1か所ずつ間違えたもの -/
def checkCases : List Game :=
  let g := Sample.game
  let r := g.rules
  let zone (f : Zone → Zone) (i : Nat) : Game := { g with rules := { r with zones := r.zones.modify i f } }
  [ g, Sample.broken,
    { g with version := 2 },
    { g with rules := { r with cardTypes := [] } },
    { g with rules := { r with cardTypes := r.cardTypes ++ ["魔法"] } },
    { g with rules := { r with handSize := 41 } },
    { g with rules := { r with zones := r.zones ++ r.zones.take 1 } },
    { g with rules := { r with zones := r.zones.filter (·.role != .grave) } },
    zone (fun z => { z with count := 0 }) 0,
    zone (fun z => { z with admits := [] }) 1,
    zone (fun z => { z with admits := ["儀式"] }) 1,
    zone (fun z => { z with onField := true }) 2,
    zone (fun z => { z with capacity := .one, count := 2 }) 3,
    { g with cards := g.cards ++ [g.cards[0]!] },
    { g with cards := [{ Sample.thunderbolt with effects := [.activated [.destroy { Sample.sel [] .opp with types := [] }]] }] },
    { g with cards := [{ Sample.skillDrain with effects := [.negate (Sample.sel ["融合"] .both)] }] },
    { g with cards := [{ Sample.drawSpell with effects := [.activated [.draw 0, .bounce (Sample.sel ["儀式"] .opp)]] }] } ]

/-- 対戦のテスト用の小さなルール（デッキ8枚・初期手札3枚） -/
def playRules : Rules := { Sample.rules with deckSize := 8, handSize := 3 }

def stateJson (g : State) : Json := json% [$(pstateJson (g true)), $(pstateJson (g false))]

def choiceJson : Choice → Json
  | .draw p => json% {kind: "draw", player: $(p)}
  | .place p h z up => json% {kind: "place", player: $(p), hand: $(h), zone: $(z), faceUp: $(up)}
  | .resolve p k e apply => json% {kind: "resolve", player: $(p), field: $(k), effect: $(e), apply: $(apply)}

/-- 動きを1つ選ぶ（できない動きも混ぜる） -/
def Rand.choice (g : State) : Rand Choice := do
  let p ← Rand.bool
  match ← Rand.next 4 with
  | 0 => return .draw p
  | 1 | 2 =>
    let h ← Rand.next ((g p).hand.length + 1)
    -- 置けるゾーンを選びやすくする
    let ok := match (g p).hand[h]? with
      | some c => (List.range playRules.zones.length).filter fun i =>
          (playRules.zones[i]?.map fun z => z.role == .plain && z.admits.contains c.type).getD false
      | none => []
    let z ← if ok.isEmpty || (← Rand.next 4) == 0 then Rand.next (playRules.zones.length + 1) else Rand.pick ok
    return .place p h z (← Rand.bool)
  | _ =>
    -- 魔法を探して発動することが多くなるように、フィールドにあるカードを選びやすくする
    let n := (g p).field.length
    let k ← if n == 0 then pure 0 else do
      let spells := (List.range n).filter fun i => ((g p).field[i]?.map (·.card.type == "魔法")).getD false
      if spells.isEmpty || (← Rand.next 4) == 0 then Rand.next (n + 1) else Rand.pick spells
    return .resolve p k (if (← Rand.next 5) == 0 then 1 else 0) ((← Rand.next 4) != 0)

def vectors : Json := Id.run do
  let (j, _) := (do
    let selector ← Rand.list 300 do
      let s ← Rand.selector
      let v ← Rand.view
      return json% {selector: $(toJson s), view: $(viewJson v), expected: $(s.matches v)}
    let destroy ← Rand.list 100 do
      let slot : Rand Slot := do
        return ⟨← Rand.next 5, ← Rand.pick vecCards, ← Rand.bool⟩
      let deck ← Rand.list (← Rand.next 3) (Rand.pick vecCards)
      let hand ← Rand.list (← Rand.next 3) (Rand.pick vecCards)
      let grave ← Rand.list (← Rand.next 3) (Rand.pick vecCards)
      let field ← Rand.list (← Rand.next 7) slot
      let s : PState := ⟨deck, hand, grave, field⟩
      let sel ← Rand.selector
      let mine ← Rand.bool
      return json% {state: $(pstateJson s), selector: $(toJson sel), mine: $(mine),
                    expected: $(pstateJson (s.destroy Sample.rules sel mine))}
    let boards ← Rand.list 150 do
      let n := (← Rand.next 6) + 1
      let insts ← Rand.list n do
        return (⟨← Rand.pick vecCards, ← Rand.bool, ← Rand.bool⟩ : Inst)
      let rel := (List.range n).map fun y => (List.range n).map fun x => instRel insts y x
      return json% {insts: $(insts.map instJson), rel: $(rel), verdict: $(verdictName (analyzeBoard insts))}
    let check := checkCases.map fun g => json% {game: $(toJson g), errors: $(g.check)}
    let play ← Rand.list 40 do
      let d1 ← Rand.list playRules.deckSize (Rand.pick vecCards)
      let d2 ← Rand.list playRules.deckSize (Rand.pick vecCards)
      let g0 := start playRules fun p => if p then d1 else d2
      let mut g := g0
      let mut steps : Array Json := #[]
      for _ in [0:40] do
        let ch ← Rand.choice g
        let next := g.step? playRules ch
        steps := steps.push (json% {choice: $(choiceJson ch), result: $(next.map stateJson)})
        g := next.getD g
      return json% {decks: [$(d1.map (·.name)), $(d2.map (·.name))], start: $(stateJson g0), steps: $(steps)}
    return json% {version: 1, rules: $(toJson Sample.rules), cards: $(toJson vecCards),
                  selector: $(selector), check: $(check), destroy: $(destroy), boards: $(boards),
                  playRules: $(toJson playRules), play: $(play)}
    : Rand Json).run 20261018
  return j

end CardGen

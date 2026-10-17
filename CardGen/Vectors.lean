import CardGen.Sample

/-!
# 差分テスト用のテストベクトル

C# のゲームエンジンが Lean の定義と同じ結果を出すかを確かめるための、入力と期待する出力の組。
`lake exe cardgen --vectors ファイル.json` で書き出す。乱数は固定の種から作るので、毎回同じ内容になる。

- `selector`：範囲の指定（`Selector.matches`）
- `check`：形式の検査（`Game.check`）。誤りの文章も一致させる
- `destroy`：破壊の動き（`PState.destroy`）
- `boards`：盤面の無効の関係（`instRel`）と判定の手続きの分類（`analyzeBoard`）

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

/-- テストに使うカード：見本の6枚と、循環のない例・自分を無効にする例の2枚 -/
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
    { g with cards := [{ Sample.skillDrain with effects := [.negate (Sample.sel ["融合"] .both)] }] } ]

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
    return json% {version: 1, rules: $(toJson Sample.rules), cards: $(toJson vecCards),
                  selector: $(selector), check: $(check), destroy: $(destroy), boards: $(boards)}
    : Rand Json).run 20261018
  return j

end CardGen

namespace CardGen

-- `csharp/vectors.json` は、ここで作るテストベクトルと同じ内容（Lean の定義を変えたら書き出し直す）
#guard_msgs in
#eval show IO Unit from do
  let s ← IO.FS.readFile "csharp/vectors.json"
  unless s == vectors.pretty ++ "\n" do
    throw (IO.userError "csharp/vectors.json が古いです。lake exe cardgen --vectors csharp/vectors.json で書き出し直してください")

end CardGen

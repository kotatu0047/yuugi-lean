import CardGen.Sample
import CardGen.Play
import CardGen.Timed
import CardGen.Turn

/-!
# 差分テスト用のテストベクトル

C# のゲームエンジンが Lean の定義と同じ結果を出すかを確かめるための、入力と期待する出力の組。
`lake exe cardgen --vectors ファイル.json` で書き出す。乱数は固定の種から作るので、毎回同じ内容になる。

- `selector`：範囲の指定（`Selector.matches`）
- `check`：形式の検査（`Game.check`）。誤りの文章も一致させる
- `destroy`：破壊の動き（`PState.destroy`）。効果を出したカードのマスとの関係（隣・同じ縦列）も含む
- `boards`：盤面の無効の関係（`instRel`）と判定の手続きの分類（`analyzeBoard`）
- `timed`：適用の時刻つきの判定の1歩（`TSys.succ`）。有効・無効と適用の順番、ターンプレイヤーをいろいろに選ぶ
- `attack`：攻撃力（`State.atkOf`）と守備力（`State.defOf`）。無効になっているカードの位置もいろいろに選ぶ
- `combat`：MTG 式の戦闘（`State.combat`）。攻撃とブロックの組み合わせ、受けているダメージもいろいろに選ぶ
- `turnPlay`：ターンのある対戦（`Match.step?`）。ターンのルール（召喚の上限・引く枚数・種類ごとの上限・
  攻撃でタップ・召喚酔い・インスタントとスタックなど）も対戦ごとに変える。マナとタップも含む
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

instance : Inhabited Side := ⟨.both⟩
instance : Inhabited Near := ⟨.any⟩
instance : Inhabited Cell := ⟨⟨0, 0⟩⟩

def vecTypes : List TypeName := ["モンスター", "魔法", "罠"]
def vecTags : List String := ["闇属性", "機械族", "戦士族"]

def Rand.selector : Rand Selector := do
  let ts ← Rand.subset vecTypes
  let types ← if ts.isEmpty then (do return [← Rand.pick vecTypes]) else pure ts
  return { types, tags := ← Rand.subset vecTags, side := ← Rand.pick [.self, .opp, .both],
           faceUpOnly := ← Rand.bool, excludeSelf := ← Rand.bool,
           near := ← Rand.pick [.any, .any, .adjacent, .sameColumn], target := (← Rand.next 4) == 0 }

def Rand.view : Rand View := do
  return { type := ← Rand.pick vecTypes, tags := ← Rand.subset vecTags, mine := ← Rand.bool,
           faceUp := ← Rand.bool, isSelf := ← Rand.bool, adjacent := ← Rand.bool, sameColumn := ← Rand.bool,
           isTarget := ← Rand.bool }

def viewJson (v : View) : Json :=
  json% {type: $(v.type), tags: $(v.tags), mine: $(v.mine), faceUp: $(v.faceUp), isSelf: $(v.isSelf),
         adjacent: $(v.adjacent), sameColumn: $(v.sameColumn), isTarget: $(v.isTarget)}

def slotJson (sl : Slot) : Json :=
  json% {zone: $(sl.zone), cell: $(sl.cell), card: $(sl.card.name), faceUp: $(sl.faceUp), damage: $(sl.damage),
         atkBonus: $(sl.atkBonus), defBonus: $(sl.defBonus)}

def srcJson (s : Src) : Json :=
  json% {player: $(s.p), cell: $(toJson s.cell), tgt: $(s.tgt.map fun (q, sl) => json% {player: $(q), slot: $(slotJson sl)})}

def pstateJson (s : PState) : Json :=
  json% {deck: $(s.deck.map (·.name)), hand: $(s.hand.map (·.name)), grave: $(s.grave.map (·.name)),
         field: $(s.field.map slotJson), life: $(s.life)}

def instJson (i : Inst) : Json := json% {card: $(i.card.name), controller: $(i.controller), faceUp: $(i.faceUp)}

def verdictName : Verdict → String
  | .ok => "ok" | .someLoop => "someLoop" | .multiStable => "multiStable"
  | .cannotHalt => "cannotHalt" | .noStable => "noStable"

/-- カードへのダメージの魔法（モンスターすべてに 1500） -/
def vecStrike : Card :=
  { name := "地割れの雨", type := "魔法", tags := [], effects := [.activated [.strike (Sample.sel ["モンスター"] .both) 1500]] }
/-- 対象を選んでターンの終わりまで攻撃力・守備力を変える魔法 -/
def vecPump : Card :=
  { name := "一時の力", type := "魔法", tags := [],
    effects := [.activated [.pump { Sample.sel ["モンスター"] .both with target := true } 800 (-1000)]] }
/-- 対象を選んで「フィールド上」でないゾーンの魔法を打ち消す罠 -/
def vecCounter : Card :=
  { name := "打ち消しの罠", type := "罠", tags := [], effects := [.activated [.counter { Sample.sel ["魔法", "罠"] .opp with target := true }]] }
/-- 守備力を変える魔法（自分のモンスターの守備力 +500） -/
def vecToughen : Card :=
  { name := "守りの加護", type := "魔法", tags := [], effects := [.toughen (Sample.sel ["モンスター"] .self) 500] }

/-- テストに使うカード：見本のカードと、循環のない例・自分を無効にする例・カードへのダメージ・守備力の変化。
ターンのある対戦のマナを試すため、半分ほどにコスト（どの色でも1・赤・緑）を、3枚に1枚ほどにタップで出る1マナを付ける
（その3枚に1枚は、赤か緑を選んで出す） -/
def vecCards : List Card :=
  (Sample.game.cards ++ [Sample.spellBreaker, Sample.selfNegator, vecStrike, vecToughen, vecPump, vecCounter]).mapIdx fun i c =>
    { c with cost := if i % 6 == 3 then 1 else 0, mana := if i % 3 == 0 then 1 + i % 2 else 0,
             manaColor := if i % 3 == 0 && i % 9 / 3 != 2 then ["赤", "緑"][i % 9 / 3]! else "",
             manaChoice := if i % 3 == 0 && i % 9 / 3 == 2 then ["赤", "緑"] else [],
             colorCost := if i % 6 == 1 then ["赤"] else if i % 6 == 2 then ["緑"] else [],
             trample := i % 5 == 0, flying := i % 4 == 3, reach := i % 7 == 2 }

/-- フィールドのカード：ゾーンは見本の 4 つと存在しない番号、マスは 0〜5。ときどきダメージを受けている -/
def Rand.slot (zones : Nat) : Rand Slot := do
  let zone ← Rand.next zones
  let cell ← Rand.next 6
  let card ← Rand.pick vecCards
  let up ← Rand.bool
  let hurt ← Rand.next 3
  let d ← Rand.next 5
  let bonus ← Rand.next 4
  return ⟨zone, cell, card, up, if hurt == 0 then d * 500 else 0, if bonus == 0 then 300 else 0,
    if bonus == 1 then -500 else 0⟩

/-- 効果を出したもの（マスは見本のマス目の上か、マス目の外か） -/
def Rand.src : Rand Src := do
  let cells := Sample.rules.allCells
  let c ← Rand.pick cells
  return ⟨← Rand.bool, if (← Rand.next 4) == 0 then none else some c, none⟩

/-- 形式の検査のテスト：見本と、1か所ずつ間違えたもの -/
def checkCases : List Game :=
  let g := Sample.game
  let r := g.rules
  let zone (f : Zone → Zone) (i : Nat) : Game := { g with rules := { r with zones := r.zones.modify i f } }
  [ g, Sample.broken,
    { g with version := 1 },
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
    zone (fun z => { z with cells := Sample.row 25 }) 1,
    zone (fun z => { z with cells := Sample.row 24 }) 0,
    zone (fun z => { z with cells := (Sample.row 26).take 3 }) 1,
    zone (fun z => { z with cells := [⟨48, 2⟩, ⟨49, 2⟩, ⟨2, 51⟩, ⟨3, 2⟩, ⟨4, 2⟩] }) 1,
    zone (fun z => { z with cells := [⟨0, 0⟩] }) 2,
    { g with cards := [{ Sample.skillDrain with effects := [.negate { Sample.sel ["モンスター"] .both with near := .adjacent }] }] },
    { g with cards := g.cards ++ [g.cards[0]!] },
    { g with cards := [{ Sample.thunderbolt with effects := [.activated [.destroy { Sample.sel [] .opp with types := [] }]] }] },
    { g with cards := [{ Sample.skillDrain with effects := [.negate (Sample.sel ["融合"] .both)] }] },
    { g with cards := [{ Sample.drawSpell with effects := [.activated [.draw 0, .bounce (Sample.sel ["儀式"] .opp)]] }] },
    { g with rules := { r with fighters := ["儀式"] } },
    { g with rules := { r with life := 0 } },
    { g with rules := { r with placeLimits := [⟨[], 0⟩, ⟨["土地", "罠"], 1⟩] } },
    { g with rules := { r with manaColors := ["赤", "赤", ""] } },
    { g with rules := { r with tagSets := [⟨"属性", ["闇属性", "闇属性"]⟩, ⟨"属性", []⟩, ⟨"", ["機械族"]⟩] } },
    { g with rules := { r with tagSets := [⟨"属性", ["闇属性"]⟩] } },
    { g with rules := { r with manaColors := ["赤"] },
             cards := [{ Sample.jinzo with colorCost := ["紫", "赤", "紫"], manaColor := "青" }] },
    { g with cards := [{ Sample.fireball with effects := [.activated [.damage 0, .heal 0]] }] },
    { g with cards := [{ Sample.darkBlessing with effects := [.boost (Sample.sel ["魔法"] .self) 0] }] },
    { g with cards := [{ Sample.darkBlessing with effects := [.toughen (Sample.sel ["魔法"] .self) 0] }] },
    { g with cards := [{ Sample.darkBlessing with effects := [.toughen { Sample.sel ["モンスター"] .self with target := true } 100] }] },
    { g with cards := [{ Sample.fireball with effects := [.activated [.pump (Sample.sel ["魔法"] .opp) 0 0,
                                                                     .counter (Sample.sel ["モンスター"] .opp)]] }] },
    { g with cards := [{ Sample.fireball with effects := [.activated [.strike (Sample.sel ["魔法"] .opp) 0]] }] },
    { g with rules := { r with instants := ["罠", "儀式"] } },
    { g with rules := { r with manaColors := ["赤"] },
             cards := [{ Sample.jinzo with manaChoice := ["赤", "紫", "赤"], manaColor := "赤" },
                       { Sample.blooD with manaChoice := ["赤"] }] } ]

/-- 対戦のテスト用の小さなルール（デッキ8枚・初期手札3枚） -/
def playRules : Rules := { Sample.rules with deckSize := 8, handSize := 3, life := 3000 }

def stateJson (g : State) : Json := json% [$(pstateJson (g true)), $(pstateJson (g false))]

def negJson (neg : List Pos) : Json := toJson (neg.map fun (q, j) => json% [$(q), $(j)])

def tgtJson (t : Option Pos) : Json := match t with
  | some (q, j) => json% [$(q), $(j)]
  | none => Json.null

/-- 対象の位置を1つ選ぶ（選ばないことも、ないカードの位置も混ぜる） -/
def Rand.tgt (g : State) : Rand (Option Pos) := do
  if (← Rand.next 4) == 0 then return none
  let q ← Rand.bool
  return some (q, ← Rand.next ((g q).field.length + 1))

def choiceJson : Choice → Json
  | .draw p => json% {kind: "draw", player: $(p)}
  | .place p h z c up => json% {kind: "place", player: $(p), hand: $(h), zone: $(z), cell: $(c), faceUp: $(up)}
  | .resolve p k e apply neg tgt => json% {kind: "resolve", player: $(p), field: $(k), effect: $(e), apply: $(apply),
      neg: $(negJson neg), tgt: $(tgtJson tgt)}
  | .attack p k t neg => json% {kind: "attack", player: $(p), field: $(k), target: $(t), neg: $(negJson neg)}
  | .combat p atk blocks neg => json% {kind: "combat", player: $(p), attackers: $(atk),
      blocks: $(blocks.map fun (j, a) => json% [$(j), $(a)]), neg: $(negJson neg)}
  | .mend => json% {kind: "mend"}
  | .settle neg => json% {kind: "settle", neg: $(negJson neg)}

/-- フィールドのカードの位置からいくつか選ぶ（ないカードの位置も混ぜる） -/
def Rand.negs (g : State) : Rand (List Pos) := do
  let all := [true, false].flatMap fun q => (List.range ((g q).field.length + 1)).map fun j => (q, j)
  all.filterM fun _ => return (← Rand.next 3) == 0

/-- 動きを1つ選ぶ（できない動きも混ぜる） -/
def Rand.choice (g : State) : Rand Choice := do
  let p ← Rand.bool
  match ← Rand.next 6 with
  | 0 => return .draw p
  | 5 =>
    if (← Rand.next 6) == 0 then
      let negs ← Rand.negs g
      return (if ← Rand.bool then .mend else .settle negs)
    -- MTG 式の戦闘：攻撃するカードと、ブロックの組み合わせ
    let n := (g p).field.length
    let atk ← Rand.list ((← Rand.next 3) + 1) (Rand.next (n + 1))
    let m := (g (!p)).field.length
    let blocks ← Rand.list (← Rand.next 3) do return (← Rand.next (m + 1), ← Rand.next (atk.length + 1))
    return .combat p atk blocks (← Rand.negs g)
  | 4 =>
    -- 攻撃：自分のフィールドのモンスターを選びやすくする
    let n := (g p).field.length
    let mons := (List.range n).filter fun i => ((g p).field[i]?.map (·.card.type == "モンスター")).getD false
    let k ← if mons.isEmpty || (← Rand.next 4) == 0 then Rand.next (n + 1) else Rand.pick mons
    let m := (g (!p)).field.length
    let t ← if (← Rand.next 3) == 0 then pure none else (some <$> Rand.next (m + 1))
    return .attack p k t (← Rand.negs g)
  | 1 | 2 =>
    let h ← Rand.next ((g p).hand.length + 1)
    -- 置けるゾーンを選びやすくする
    let ok := match (g p).hand[h]? with
      | some c => (List.range playRules.zones.length).filter fun i =>
          (playRules.zones[i]?.map fun z => z.role == .plain && z.admits.contains c.type).getD false
      | none => []
    let z ← if ok.isEmpty || (← Rand.next 4) == 0 then Rand.next (playRules.zones.length + 1) else Rand.pick ok
    -- 空いているマスを選びやすくする
    let c ← if (← Rand.next 3) == 0 then Rand.next 6 else pure (g.freeCell playRules p z)
    return .place p h z c (← Rand.bool)
  | _ =>
    -- 魔法を探して発動することが多くなるように、フィールドにあるカードを選びやすくする
    let n := (g p).field.length
    let k ← if n == 0 then pure 0 else do
      let spells := (List.range n).filter fun i => ((g p).field[i]?.map (·.card.type == "魔法")).getD false
      if spells.isEmpty || (← Rand.next 4) == 0 then Rand.next (n + 1) else Rand.pick spells
    return .resolve p k (if (← Rand.next 5) == 0 then 1 else 0) ((← Rand.next 4) != 0) (← Rand.negs g) (← Rand.tgt g)

def turnJson (t : TurnInfo) : Json :=
  json% {tp: $(t.tp), count: $(t.count), summons: $(t.summons), attacked: $(t.attacked.map slotJson),
         placed: $(t.placed), entered: $(t.entered.map slotJson), pool: $(t.pool), oppPool: $(t.oppPool),
         tapped: $(t.tapped.map slotJson), oppTapped: $(t.oppTapped.map slotJson),
         attackers: $(t.attackers.map slotJson), blocked: $(t.blocked.map slotJson),
         stack: $(t.stack.map fun (q, sl) => json% [$(q), $(slotJson sl)]), made: $(t.made), spent: $(t.spent),
         decked: $(t.decked), prio: $(t.prio), passes: $(t.passes)}

def tchoiceJson : TChoice → Json
  | .place h z c up pay => json% {kind: "place", hand: $(h), zone: $(z), cell: $(c), faceUp: $(up), pay: $(pay)}
  | .cast h z c up pay => json% {kind: "cast", hand: $(h), zone: $(z), cell: $(c), faceUp: $(up), pay: $(pay)}
  | .resolve p k e apply neg tgt => json% {kind: "resolve", player: $(p), field: $(k), effect: $(e), apply: $(apply),
      neg: $(negJson neg), tgt: $(tgtJson tgt)}
  | .attack k t neg => json% {kind: "attack", field: $(k), target: $(t), neg: $(negJson neg)}
  | .settle neg => json% {kind: "settle", neg: $(negJson neg)}
  | .tap k color => json% {kind: "tap", field: $(k), color: $(color)}
  | .oppTap k color => json% {kind: "oppTap", field: $(k), color: $(color)}
  | .block blocks neg => json% {kind: "block", blocks: $(blocks.map fun (j, a) => json% [$(j), $(a)]),
      neg: $(negJson neg)}
  | .pass => json% {kind: "pass"}
  | .endTurn => json% {kind: "endTurn"}

/-- ターンのある対戦のテストのゾーン：見本のゾーンに、「フィールド上」でない魔法・罠のゾーン（スタック）を加えたもの -/
def turnZones : List Zone :=
  playRules.zones ++ [{ name := "スタック", count := 1, capacity := .many, role := .plain, onField := false,
                        admits := ["魔法", "罠"] }]

/-- `c` を置けるゾーン -/
def zonesFor (r : Rules) (c : Card) : List Nat :=
  (List.range r.zones.length).filter fun i =>
    (r.zones[i]?.map fun z => z.role == .plain && z.admits.contains c.type).getD false

/-- マナを出すカードの位置と色（2色以上から選べるなら、どれか） -/
def Rand.tapOf (f : List Slot) : Rand (Nat × String) := do
  let ms := (List.range f.length).filter fun i => (f[i]?.map fun (sl : Slot) => decide (0 < sl.card.mana)).getD false
  let k ← if ms.isEmpty || (← Rand.next 5) == 0 then Rand.next (f.length + 1) else Rand.pick ms
  let color ← match f[k]? with
    | some sl => if sl.card.manaChoice.isEmpty || (← Rand.next 6) == 0 then Rand.pick ["", "赤", "緑", "白"]
                 else Rand.pick sl.card.manaChoice
    | none => pure ""
  return (k, color)

/-- 手札の `h` 番目を置く動き（払うマナは、たいていは自動の払い方、ときどき持っているマナから適当に選ぶ） -/
def Rand.placeArgs (r : Rules) (g : State) (p : PlayerId) (pool : List String) (h : Nat) :
    Rand (Nat × Nat × Bool × List String) := do
  let (z, c) ← match (g p).hand[h]? with
    | some card =>
      let zs := zonesFor r card
      let z ← if zs.isEmpty || (← Rand.next 6) == 0 then Rand.next (r.zones.length + 1) else Rand.pick zs
      let c ← if (← Rand.next 5) == 0 then Rand.next 6 else pure (g.freeCell r p z)
      pure (z, c)
    | none => pure (0, 0)
  let pay ← match (g p).hand[h]?.bind (autoPay · pool) with
    | some pay => if (← Rand.next 5) == 0 then Rand.subset pool else pure pay
    | none => Rand.subset pool
  return (z, c, (← Rand.next 4) != 0, pay)

/-- ターンのある対戦の動きを1つ選ぶ（できない動きも混ぜる）。攻撃は、ターンプレイヤーの戦闘できるカードと、
攻撃できる対象を選びやすくする -/
def Rand.tchoice (r : Rules) (m : Match) : Rand TChoice := do
  let tp := m.turn.tp
  let o := (m.g (!tp)).field
  let fighters := (List.range o.length).filter fun j => (o[j]?.map r.fights).getD false
  -- 優先権：ときどきパスする。スタックがあるか攻撃の途中で、両者がまだパスしていなければ、パスを多くする
  if (← Rand.next 10) == 0 then return .pass
  if m.turn.passes < 2 && !m.turn.quiet && (← Rand.next 3) != 0 then return .pass
  -- 優先権を持つのがターンプレイヤーでなければ、たいていはインスタント・タップ・発動かパス
  if m.turn.prio != tp && m.turn.passes < 2 && (← Rand.next 4) != 0 then
    match ← Rand.next 5 with
    | 0 | 4 => return .pass
    | 1 =>
      let f := (m.g (!tp)).field
      return .resolve (!tp) (← Rand.next (f.length + 1)) 0 ((← Rand.next 4) != 0) (← Rand.negs m.g) (← Rand.tgt m.g)
    | 2 =>
      let (k, color) ← Rand.tapOf o
      return .oppTap k color
    | _ =>
      let hand := (m.g (!tp)).hand
      let h ← Rand.next (hand.length + 1)
      let (z, c, up, pay) ← Rand.placeArgs r m.g (!tp) m.turn.oppPool h
      return .cast h z c up pay
  -- スタックがあれば、たいていは一番上を解決する
  if let some (q, top) := m.turn.stack.head? then
    if (← Rand.next 3) != 0 then
      let f := (m.g q).field
      let k := ((List.range f.length).find? fun i => (f[i]?.map Slot.base) == some top).getD 0
      return .resolve q k 0 ((← Rand.next 4) != 0) (← Rand.negs m.g) (← Rand.tgt m.g)
  -- ブロックを待っているときは、たいていブロックを選ぶ（戦闘できるカードを選びやすくする）
  if !m.turn.attackers.isEmpty && (← Rand.next 3) != 0 then
    let n ← Rand.next 3
    let blocks ← Rand.list n do
      let j ← if fighters.isEmpty || (← Rand.next 5) == 0 then Rand.next (o.length + 1) else Rand.pick fighters
      return (j, ← Rand.next (m.turn.attackers.length + 1))
    return .block blocks (← Rand.negs m.g)
  -- ターンプレイヤーでない方：インスタントを置く・タップする
  if (← Rand.next 8) == 0 then
    let hand := (m.g (!tp)).hand
    if (← Rand.bool) && !hand.isEmpty then
      let h ← Rand.next hand.length
      let (z, c, up, pay) ← Rand.placeArgs r m.g (!tp) m.turn.oppPool h
      return .cast h z c up pay
    let (k, color) ← Rand.tapOf o
    return .oppTap k color
  -- マナがあれば、払えるカードを置くことを多くする
  let hand := (m.g tp).hand
  let payable := (List.range hand.length).filter fun h => (hand[h]?.bind (autoPay · m.turn.pool)).isSome
  if !m.turn.pool.isEmpty && !payable.isEmpty && (← Rand.bool) then
    let h ← Rand.pick payable
    let c := hand[h]!
    let zs := zonesFor r c
    let z ← if zs.isEmpty then pure 0 else Rand.pick zs
    return .place h z (m.g.freeCell r tp z) true ((autoPay c m.turn.pool).getD [])
  match ← Rand.next 15 with
  | 0 => return .endTurn
  | 10 | 11 | 12 | 13 | 14 => do
    let (k, color) ← Rand.tapOf (m.g tp).field
    return .tap k color
  | 1 | 2 | 3 | 7 | 8 => do
    let f := (m.g tp).field
    let mons := (List.range f.length).filter fun i => (f[i]?.map fun sl => sl.faceUp && r.fights sl).getD false
    let k ← if mons.isEmpty || (← Rand.next 5) == 0 then Rand.next (f.length + 1) else Rand.pick mons
    let t ← if r.blocking && (← Rand.next 5) != 0 then pure none
      else if fighters.isEmpty || (← Rand.next 5) == 0 then
        (if (← Rand.bool) then pure none else some <$> Rand.next (o.length + 1))
      else some <$> Rand.pick fighters
    return .attack k t (← Rand.negs m.g)
  | 4 | 5 | 6 => do
    -- 置く
    let h ← Rand.next (hand.length + 1)
    let (z, c, up, pay) ← Rand.placeArgs r m.g tp m.turn.pool h
    return .place h z c up pay
  | _ => do
    -- 発動：ターンプレイヤーのカードが多く、ときどき相手のカードも
    let q := if (← Rand.next 4) == 0 then !tp else tp
    let f := (m.g q).field
    let k ← if f.isEmpty then pure 0 else do
      let spells := (List.range f.length).filter fun i => ((f[i]?.map (·.card.type == "魔法")).getD false)
      if spells.isEmpty || (← Rand.next 4) == 0 then Rand.next (f.length + 1) else Rand.pick spells
    if (← Rand.next 12) == 0 then return .settle (← Rand.negs m.g)
    return .resolve q k (if (← Rand.next 5) == 0 then 1 else 0) ((← Rand.next 4) != 0) (← Rand.negs m.g) (← Rand.tgt m.g)

def vectors (_ : Unit := ()) : Json := Id.run do
  let (j, _) := (do
    let selector ← Rand.list 300 do
      let s ← Rand.selector
      let v ← Rand.view
      return json% {selector: $(toJson s), view: $(viewJson v), expected: $(s.matches v)}
    let destroy ← Rand.list 100 do
      let slot := Rand.slot 5
      let deck ← Rand.list (← Rand.next 3) (Rand.pick vecCards)
      let hand ← Rand.list (← Rand.next 3) (Rand.pick vecCards)
      let grave ← Rand.list (← Rand.next 3) (Rand.pick vecCards)
      let field ← Rand.list (← Rand.next 7) slot
      let s : PState := ⟨deck, hand, grave, field, ← Rand.next 9000⟩
      let sel ← Rand.selector
      let q ← Rand.bool
      let src0 ← Rand.src
      -- 対象：ときどきフィールドのカードの1枚を選ぶ
      let who ← Rand.pick [q, !q]
      let i ← Rand.next (field.length + 1)
      let coin ← Rand.next 2
      let src : Src := match field[i]? with
        | some t => if coin == 0 then src0 else { src0 with tgt := some (who, t.base) }
        | none => src0
      return json% {state: $(pstateJson s), selector: $(toJson sel), owner: $(q), src: $(srcJson src),
                    expected: $(pstateJson (s.destroy Sample.rules sel q src))}
    let boards ← Rand.list 150 do
      let n := (← Rand.next 6) + 1
      let insts ← Rand.list n do
        return (⟨← Rand.pick vecCards, ← Rand.bool, ← Rand.bool⟩ : Inst)
      let rel := (List.range n).map fun y => (List.range n).map fun x => instRel insts y x
      return json% {insts: $(insts.map instJson), rel: $(rel), verdict: $(verdictName (analyzeBoard insts))}
    let timed ← Rand.list 200 do
      let n := (← Rand.next 5) + 1
      let insts ← Rand.list n do
        return (⟨← Rand.pick vecCards, ← Rand.bool, ← Rand.bool⟩ : Inst)
      let s : TState := ⟨← Rand.list n Rand.bool, ← Rand.pick (perms (List.range n))⟩
      let tp ← Rand.bool
      let tjson (t : TState) : Json := json% {on: $(t.on), order: $(t.order)}
      return json% {insts: $(insts.map instJson), state: $(tjson s), turn: $(tp),
                    expected: $((TSys.ofInsts insts).succ tp s |>.map tjson)}
    let attack ← Rand.list 100 do
      let slot := Rand.slot 3
      let f1 ← Rand.list (← Rand.next 6) slot
      let f2 ← Rand.list (← Rand.next 6) slot
      let g : State := fun p => ⟨[], [], [], if p then f1 else f2, 0⟩
      let neg ← Rand.negs g
      let atks := [true, false].map fun q =>
        (List.range (g q).field.length).map fun j =>
          ((g q).field[j]?.map fun sl => g.atkOf Sample.rules neg (q, j) sl).getD 0
      let defs := [true, false].map fun q =>
        (List.range (g q).field.length).map fun j =>
          ((g q).field[j]?.map fun sl => g.defOf Sample.rules neg (q, j) sl).getD 0
      return json% {state: $(stateJson g), neg: $(negJson neg), expected: $(atks), defense: $(defs)}
    let combat ← Rand.list 150 do
      let slot := Rand.slot 3
      let f1 ← Rand.list (← Rand.next 5) slot
      let f2 ← Rand.list (← Rand.next 5) slot
      let g : State := fun p => ⟨[], [], [], if p then f1 else f2, 8000⟩
      let neg ← Rand.negs g
      let p ← Rand.bool
      let atk ← Rand.list ((← Rand.next 3) + 1) (Rand.next ((g p).field.length + 1))
      let blocks ← Rand.list (← Rand.next 4) do
        return (← Rand.next ((g (!p)).field.length + 1), ← Rand.next (atk.length + 1))
      return json% {state: $(stateJson g), neg: $(negJson neg), player: $(p), attackers: $(atk),
                    blocks: $(blocks.map fun (j, a) => json% [$(j), $(a)]),
                    expected: $(stateJson (g.combat Sample.rules neg p atk blocks))}
    let check := checkCases.map fun g => json% {game: $(toJson g), errors: $(g.check)}
    let play ← Rand.list 80 do
      let d1 ← Rand.list playRules.deckSize (Rand.pick vecCards)
      let d2 ← Rand.list playRules.deckSize (Rand.pick vecCards)
      let g0 := start playRules fun p => if p then d1 else d2
      let mut g := g0
      let mut steps : Array Json := #[]
      for _ in [0:50] do
        let ch ← Rand.choice g
        let next := g.step? playRules ch
        steps := steps.push (json% {choice: $(choiceJson ch), result: $(next.map stateJson)})
        g := next.getD g
      return json% {decks: [$(d1.map (·.name)), $(d2.map (·.name))], start: $(stateJson g0), steps: $(steps)}
    let turnPlay ← Rand.list 80 do
      let r : Rules := { playRules with
        summonsPerTurn := ← Rand.next 3, drawPerTurn := ← Rand.next 3,
        firstTurnDraw := ← Rand.bool, firstTurnAttack := ← Rand.bool,
        placeLimits := ← Rand.pick [[], [⟨["罠"], 1⟩], [⟨["魔法", "罠"], 2⟩, ⟨["モンスター"], 1⟩]],
        attackTaps := ← Rand.bool, summoningSickness := ← Rand.bool, blocking := ← Rand.bool,
        instants := ← Rand.pick [[], ["罠"], ["魔法", "罠"]], stack := ← Rand.bool, zones := turnZones,
        life := ← Rand.pick [8000, 0], deckSize := 20 }
      let d1 ← Rand.list r.deckSize (Rand.pick vecCards)
      let d2 ← Rand.list r.deckSize (Rand.pick vecCards)
      let first ← Rand.bool
      let m0 := Match.start r (fun p => if p then d1 else d2) first
      let mut m := m0
      let mut steps : Array Json := #[]
      for _ in [0:60] do
        let ch ← Rand.tchoice r m
        let next := m.step? r ch
        steps := steps.push (json% {choice: $(tchoiceJson ch),
          result: $(next.map fun m' => json% {state: $(stateJson m'.g), turn: $(turnJson m'.turn)})})
        m := next.getD m
      return json% {rules: $(toJson r), decks: [$(d1.map (·.name)), $(d2.map (·.name))], first: $(first),
                    start: {state: $(stateJson m0.g), turn: $(turnJson m0.turn)}, steps: $(steps)}
    return json% {version: 1, rules: $(toJson Sample.rules), cards: $(toJson vecCards),
                  selector: $(selector), check: $(check), destroy: $(destroy), boards: $(boards), timed: $(timed), attack: $(attack),
                  combat: $(combat),
                  playRules: $(toJson playRules), play: $(play), turnPlay: $(turnPlay)}
    : Rand Json).run 20261018
  return j

end CardGen

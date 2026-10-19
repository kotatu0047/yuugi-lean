import CardGen.Sample

/-!
# MTG 風の見本

マナ・タップ・召喚酔い・ブロック（MTG 式の戦闘）・インスタントとスタックを使う、MTG に似たゲームの見本。
マナは5色（白・青・黒・赤・緑）で、基本土地はそれぞれ1色のマナを出し、カープルーザンの森は赤か緑を選んで出す。
コストは「どの色でも払える分」と「色の決まった分」に分かれる（灰色熊は 1 ＋ 緑）。カードの種類は土地・クリーチャー・
インスタント・ソーサリー・エンチャントで、インスタントとソーサリーは「スタック」のゾーンに置いてから発動する
（フィールド上には数えない）。

- デッキ（ライブラリー）40枚・初期手札7枚・ライフ20・1ターンに1枚引く（先攻の最初のターンは引かない）
- 戦場は1人20マス（2行×10列）。土地は1ターンに1枚まで。土地をタップして1マナを出し、カードのコストを払って置く
- クリーチャーは召喚酔いがあり、攻撃するとタップする。タップしているクリーチャーは、持ち主の次のターンまで攻撃もブロックもできない
- 攻撃するクリーチャーを宣言し（何体でもよい）、攻撃されたプレイヤーがブロックするクリーチャーを選ぶ（1体の攻撃を
  何体でブロックしてもよい）。ブロックされたら、攻撃力（パワー）と守備力（タフネス）で互いにダメージを与え、
  守備力以上のダメージを受けたクリーチャーを破壊する。ブロックされなければ攻撃力のダメージ。ダメージはターンの終わりまで残る
- インスタントは、相手のターンや、攻撃・スタックへの応答としても置ける（相手のターンには、自分の土地をタップして払う）。
  インスタントとソーサリーはスタックに積まれ、後に置いたものから解決する。スタックが空になるまで、ほかのことはできない
- ライブラリーから引けなければ負け

- 対象を1つ選ぶ効果（ショック・巨大化・対抗呪文）は、解決するときに範囲に合うカードを1枚選ぶ
- 巨大化は、ターンの終わりまで攻撃力・守備力を変える。対抗呪文は、スタックにある呪文を打ち消す
- 飛行を持つクリーチャー（風のドレイク）は、飛行か到達（巨大蜘蛛）を持つクリーチャーでしかブロックできない
- 守備力が 0 になったクリーチャーは、状態の確認で破壊される

実際の MTG との違い（このプロトタイプで表せないもの）：プレイヤーを対象に選ぶこと（稲妻は相手にだけダメージを与える）、
対象は唱えるときではなく解決するときに選ぶこと、優先権の順番（ここではどちらのプレイヤーも、いつでもインスタントを置ける）、
飛行・到達・トランプル以外の能力。

同じ内容の JSON が `CardGen/mtg.json` にある。
-/

namespace CardGen.Mtg
open Lean Sample

def land : TypeName := "土地"
def creature : TypeName := "クリーチャー"
def instant : TypeName := "インスタント"
def sorcery : TypeName := "ソーサリー"
def enchantment : TypeName := "エンチャント"

/-- 戦場のマス：行 26 と 27 の、列 19〜28（相手は点対称の、行 22 と 21） -/
def battlefield : List Cell := (List.range 20).map fun i => ⟨19 + i % 10, 26 + i / 10⟩

def rules : Rules where
  cardTypes := [land, creature, instant, sorcery, enchantment]
  deckSize := 40
  handSize := 7
  zones := [
    { name := "戦場", count := 20, capacity := .one, role := .plain, onField := true,
      admits := [land, creature, enchantment], cells := battlefield },
    { name := "スタック", count := 1, capacity := .many, role := .plain, onField := false, admits := [instant, sorcery] },
    { name := "ライブラリー", count := 1, capacity := .many, role := .deck, onField := false,
      admits := [land, creature, instant, sorcery, enchantment] },
    { name := "墓地", count := 1, capacity := .many, role := .grave, onField := false,
      admits := [land, creature, instant, sorcery, enchantment] }]
  life := 20
  fighters := [creature]
  summonsPerTurn := 0
  firstTurnAttack := true
  placeLimits := [⟨[land], 1⟩]
  attackTaps := true
  summoningSickness := true
  blocking := true
  manaColors := ["白", "青", "黒", "赤", "緑"]
  tagSets := [⟨"色", ["白", "青", "黒", "赤", "緑"]⟩, ⟨"クリーチャー・タイプ", ["騎士", "熊", "ゴブリン", "巨人"]⟩]
  instants := [instant]
  stack := true

def mountain : Card := { name := "山", type := land, tags := [], effects := [], mana := 1, manaColor := "赤" }
def forest : Card := { name := "森", type := land, tags := [], effects := [], mana := 1, manaColor := "緑" }
def plains : Card := { name := "平地", type := land, tags := [], effects := [], mana := 1, manaColor := "白" }
def island : Card := { name := "島", type := land, tags := [], effects := [], mana := 1, manaColor := "青" }
/-- 赤か緑を選んで出す土地 -/
def karplusan : Card :=
  { name := "カープルーザンの森", type := land, tags := [], effects := [], mana := 1, manaChoice := ["赤", "緑"] }

def goblin : Card :=
  { name := "ゴブリンの先兵", type := creature, tags := ["赤", "ゴブリン"], effects := [], attack := 1, defense := 1,
    colorCost := ["赤"] }
def bear : Card :=
  { name := "灰色熊", type := creature, tags := ["緑", "熊"], effects := [], attack := 2, defense := 2,
    cost := 1, colorCost := ["緑"] }
def giant : Card :=
  { name := "丘巨人", type := creature, tags := ["赤", "巨人"], effects := [], attack := 3, defense := 3,
    cost := 3, colorCost := ["赤"] }
/-- トランプルを持つ -/
def rhino : Card :=
  { name := "大角のサイ", type := creature, tags := ["緑"], effects := [], attack := 4, defense := 4,
    cost := 2, colorCost := ["緑", "緑"], trample := true }
def knight : Card :=
  { name := "白騎士", type := creature, tags := ["白", "騎士"], effects := [], attack := 2, defense := 2,
    colorCost := ["白", "白"] }

/-- 飛行を持つ -/
def drake : Card :=
  { name := "風のドレイク", type := creature, tags := ["青"], effects := [], attack := 2, defense := 2,
    cost := 2, colorCost := ["青"], flying := true }
/-- 到達を持つ -/
def spider : Card :=
  { name := "巨大蜘蛛", type := creature, tags := ["緑"], effects := [], attack := 2, defense := 4,
    cost := 3, colorCost := ["緑"], reach := true }

/-- 対象を1つ選ぶ範囲 -/
def target (types : List TypeName) (side : Side) : Selector := { sel types side with target := true }

def shock : Card :=
  { name := "ショック", type := instant, tags := ["赤"], effects := [.activated [.strike (target [creature] .both) 2]],
    colorCost := ["赤"] }
def growth : Card :=
  { name := "巨大化", type := instant, tags := ["緑"], effects := [.activated [.pump (target [creature] .both) 3 3]],
    colorCost := ["緑"] }
def counterspell : Card :=
  { name := "対抗呪文", type := instant, tags := ["青"], effects := [.activated [.counter (target [instant, sorcery] .opp)]],
    colorCost := ["青", "青"] }

def bolt : Card :=
  { name := "稲妻", type := instant, tags := ["赤"], effects := [.activated [.damage 3]], colorCost := ["赤"] }
def pyroclasm : Card :=
  { name := "紅蓮地獄", type := sorcery, tags := ["赤"], effects := [.activated [.strike (sel [creature] .both) 2]],
    cost := 1, colorCost := ["赤"] }
def wrath : Card :=
  { name := "神の怒り", type := sorcery, tags := ["白"],
    effects := [.activated [.destroy (sel [creature] .both)]], cost := 2, colorCost := ["白", "白"] }
def unsummon : Card :=
  { name := "送還の波", type := sorcery, tags := ["青"],
    effects := [.activated [.bounce (sel [creature] .opp)]], cost := 3, colorCost := ["青"] }
def divination : Card :=
  { name := "予言", type := sorcery, tags := ["青"], effects := [.activated [.draw 2]], cost := 1, colorCost := ["青"] }
def salve : Card :=
  { name := "治癒の軟膏", type := instant, tags := ["白"], effects := [.activated [.heal 4]], colorCost := ["白"] }
def anthem : Card :=
  { name := "栄光の頌歌", type := enchantment, tags := ["白"],
    effects := [.boost (sel [creature] .self) 1, .toughen (sel [creature] .self) 1], cost := 2, colorCost := ["白"] }
def silence : Card :=
  { name := "沈黙の結界", type := enchantment, tags := ["白"],
    effects := [.negate (sel [enchantment] .opp)], cost := 1, colorCost := ["白"] }

def game : Game where
  version := currentVersion
  rules := rules
  cards := [mountain, forest, plains, island, karplusan, goblin, bear, giant, rhino, knight, drake, spider, bolt, shock,
            growth, counterspell, pyroclasm, wrath, unsummon, divination, salve, anthem, silence]

/-! ## 検査 -/

#guard game.WellFormed
#guard rules.allCells.length == 40 && (dups rules.allCells).isEmpty

-- `mtg.json` は見本と同じ内容（Unity のエディタが「見本（MTG 風）」で読み込む写しも同じ）
#guard_msgs in
#eval show IO Unit from do
  let s ← IO.FS.readFile "CardGen/mtg.json"
  match Game.parse s with
  | .ok g => unless g == game do throw (IO.userError "mtg.json が見本と違います")
  | .error e => throw (IO.userError e)
  let u ← IO.FS.readFile "unity/CardGenEditor/Assets/CardGenEditor/Resources/mtg.json"
  unless u == s do throw (IO.userError "Unity の Resources/mtg.json が CardGen/mtg.json と違います")

-- ★：土地は1ターンに1枚まで、払うマナはタップで出したマナを超えない
#guard ((report (toJson game).compress).claims.map (·.text)).contains "「土地」を置けるのは、1ターンに 1 枚まで"
#guard ((report (toJson game).compress).claims.map (·.theorem)).contains "CardGen.TReachable.spent_le"

-- 形式の検査：永続効果の範囲では対象を選べない。打ち消す範囲は「フィールド上」でないゾーンに置ける種類
#guard !({ game with cards := [{ anthem with effects := [.boost (target [creature] .self) 1] }] }).WellFormed
#guard !({ game with cards := [{ counterspell with effects := [.activated [.counter (target [creature] .opp)]] }] }).WellFormed
-- 形式の検査：選べるマナの色と、カードへのダメージ
#guard !({ game with cards := [{ karplusan with manaChoice := ["赤", "紫"] }] }).WellFormed
#guard !({ game with cards := [{ karplusan with manaColor := "赤" }] }).WellFormed
#guard !({ game with cards := [{ pyroclasm with effects := [.activated [.strike (sel [land] .both) 2]] }] }).WellFormed
#guard !({ game with rules := { rules with instants := ["呪文"] } }).WellFormed

/-! ## 対戦 -/

/-- 手札7枚：山・山・ゴブリンの先兵・灰色熊・稲妻・山・森。そのあと引くのは山・灰色熊・…… -/
def deck : List Card :=
  [mountain, mountain, goblin, bear, bolt, mountain, forest] ++
  (List.range 33).map fun i => if i % 2 == 0 then mountain else bear

def m0 : Match := Match.start rules (fun _ => deck) true

/-- 1ターン目：山を置き、タップして赤マナを出し、それでゴブリンの先兵（赤）を置く -/
def turn1 : List TChoice := [.place 0 0 0 true, .tap 0, .place 1 0 1 true ["赤"]]

#guard match Match.run rules m0 turn1 with
  | some m => (m.g true).field.map (·.card.name) == ["山", "ゴブリンの先兵"] && m.turn.pool == [] &&
      m.turn.made == 1 && m.turn.spent == 1
  | none => false
-- 土地は1ターンに1枚まで。マナが足りなければ置けない（灰色熊は 1 ＋ 緑）。同じマスには置けない
#guard (Match.run rules m0 [.place 0 0 0 true, .place 0 0 1 true]).isNone
#guard (Match.run rules m0 [.place 0 0 0 true, .tap 0, .place 2 0 1 true ["赤"]]).isNone
#guard (Match.run rules m0 [.place 0 0 0 true, .tap 0, .place 1 0 0 true ["赤"]]).isNone
-- 色が違えば払えない：森を置いて緑マナを出しても、ゴブリンの先兵（赤）は置けない
#guard (Match.run rules m0 [.place 6 0 0 true, .tap 0, .place 2 0 1 true ["緑"]]).isNone
#guard (Match.run rules m0 [.place 6 0 0 true, .tap 0, .place 2 0 1 true ["赤"]]).isNone
-- 3ターン目に森を置けば、山と森で灰色熊（1 ＋ 緑）を置ける。どの色でも払える分は赤で払う
#guard match Match.run rules m0
    (turn1 ++ [.endTurn] ++ turn1 ++ [.endTurn, .place 4 0 2 true, .tap 0, .tap 2]) with
  | some m => m.turn.pool == ["赤", "緑"] && autoPay bear m.turn.pool == some ["緑", "赤"] &&
      autoPay giant m.turn.pool == none &&
      ((m.step? rules (.place 1 0 3 true ["緑", "赤"])).map fun m' => m'.turn.pool) == some []
  | none => false
-- 召喚酔い：置いたターンには攻撃できない
#guard (Match.run rules m0 (turn1 ++ [.attack 1 none []])).isNone

/-- 2ターン目（相手）：同じように山とゴブリンの先兵。3ターン目（自分）：ゴブリンの先兵で攻撃を宣言し、
両者がパスする（相手がブロックを選ぶ番になる） -/
def toAttack : List TChoice := turn1 ++ [.endTurn] ++ turn1 ++ [.endTurn, .attack 1 none [], .pass, .pass]

-- 両者がパスするまでは、ブロックを選べない
#guard (Match.run rules m0 (turn1 ++ [.endTurn] ++ turn1 ++ [.endTurn, .attack 1 none [], .block [] []])).isNone
-- 攻撃を宣言すると、相手がブロックを選ぶまで待つ（ターン終了やソーサリー速度のカードを置くことはできない）
#guard match Match.run rules m0 toAttack with
  | some m => m.turn.attackers.length == 1
  | none => false
#guard (Match.run rules m0 (toAttack ++ [.endTurn])).isNone
-- ブロックしなければ、攻撃力の 1 点のダメージ
#guard match Match.run rules m0 (toAttack ++ [.block [] []]) with
  | some m => (m.g false).life == 19 && m.turn.attackers.isEmpty
  | none => false
-- 相手のゴブリンの先兵でブロックすると、互いに 1 点のダメージで両方とも破壊される（プレイヤーへのダメージはない）
#guard match Match.run rules m0 (toAttack ++ [.block [(1, 0)] []]) with
  | some m => (m.g true).field.length == 1 && (m.g false).field.length == 1 && (m.g false).life == 20 &&
      (m.g true).grave == [goblin] && (m.g false).grave == [goblin]
  | none => false
-- 戦闘できないカード（山）ではブロックできない。同じカードで2回はブロックできない
#guard (Match.run rules m0 (toAttack ++ [.block [(0, 0)] []])).isNone
#guard (Match.run rules m0 (toAttack ++ [.block [(1, 0), (1, 0)] []])).isNone
-- 攻撃したゴブリンの先兵はタップしたまま。相手のターンには、ブロックできない
#guard (Match.run rules m0 (toAttack ++ [.block [] [], .endTurn, .attack 1 none [], .pass, .pass, .block [(1, 0)] []])).isNone
#guard match Match.run rules m0 (toAttack ++ [.block [] [], .endTurn, .attack 1 none [], .pass, .pass, .block [] []]) with
  | some m => (m.g true).life == 19 && (m.g false).life == 19
  | none => false

/-! ## 戦闘のダメージ -/

def slot (i : Nat) (c : Card) (damage : Nat := 0) : Slot := ⟨0, i, c, true, damage, 0, 0⟩

def board (mine opp : List Slot) : State := fun p =>
  { deck := [], hand := [], grave := [], life := 20, field := if p then mine else opp }

-- 熊（2/2）がゴブリンの先兵（1/1）にブロックされると、ゴブリンの先兵だけが破壊され、熊は 1 点のダメージが残る
#guard match (board [slot 0 bear] [slot 0 goblin]).step? rules (.attack true 0 (some 0) []) with
  | some g => (g true).field == [slot 0 bear 1] && (g false).field.isEmpty
  | none => false
-- ダメージは残る：すでに 2 点のダメージを受けている丘巨人（3/3）は、ゴブリンの先兵の 1 点で破壊される
#guard match (board [slot 0 giant 2] [slot 0 goblin]).step? rules (.combat true [0] [(0, 0)] []) with
  | some g => (g true).field.isEmpty && (g false).field.isEmpty
  | none => false
-- 複数でのブロック：丘巨人（攻撃力 3）をゴブリンの先兵2体でブロックすると、1体目に 1 点（破壊できるだけ）、
-- 2体目に残りの 2 点を与えて両方とも破壊し、自分は 2 点のダメージを受けて残る
#guard match (board [slot 0 giant] [slot 0 goblin, slot 1 goblin]).step? rules (.combat true [0] [(0, 0), (1, 0)] []) with
  | some g => (g true).field == [slot 0 giant 2] && (g false).field.isEmpty
  | none => false
-- まとめて攻撃：ゴブリンの先兵と熊で攻撃し、熊だけをブロックすると、相手はゴブリンの先兵の 1 点を受ける
#guard match (board [slot 0 goblin, slot 1 bear] [slot 0 bear]).step? rules (.combat true [0, 1] [(0, 1)] []) with
  | some g => (g false).life == 19 && (g true).field == [slot 0 goblin] && (g false).field.isEmpty
  | none => false
-- トランプル：大角のサイ（4/4）がゴブリンの先兵（1/1）にブロックされると、ゴブリンの先兵に 1 点、相手に残りの 3 点。
-- トランプルがなければ、4 点ともゴブリンの先兵に与える
#guard match (board [slot 0 rhino] [slot 0 goblin]).step? rules (.combat true [0] [(0, 0)] []) with
  | some g => (g false).life == 17 && (g false).field.isEmpty && (g true).field == [slot 0 rhino 1]
  | none => false
#guard match (board [slot 0 { rhino with trample := false }] [slot 0 goblin]).step? rules (.combat true [0] [(0, 0)] []) with
  | some g => (g false).life == 20
  | none => false
-- 栄光の頌歌（自分のクリーチャーの攻撃力・守備力 +1）：ゴブリンの先兵は 2/2 になり、熊（2/2）と相打ちになる。
-- 頌歌が無効なら 1/1 のまま
#guard (board [slot 0 goblin, slot 1 anthem] []).defOf rules [] (true, 0) (slot 0 goblin) == 2
#guard (board [slot 0 goblin, slot 1 anthem] []).defOf rules [(true, 1)] (true, 0) (slot 0 goblin) == 1
#guard match (board [slot 0 bear, slot 1 anthem] [slot 0 bear]).step? rules (.combat true [0] [(0, 0)] []) with
  | some g => (g true).field == [slot 0 bear 2, slot 1 anthem] && (g false).field.isEmpty
  | none => false
-- ダメージを消す
#guard ((board [slot 0 giant 2] []).mend true).field == [slot 0 giant]

/-! ## 対象・ターンの終わりまでの変化・打ち消し・飛行 -/

-- ショック（対象を1つ選ぶ）：ゴブリンの先兵2体のうち、選んだ1体だけに 2 点
#guard match (board [⟨1, 0, shock, true, 0, 0, 0⟩] [slot 0 goblin, slot 1 goblin]).step? rules
    (.resolve true 0 0 true [] (some (false, 1))) with
  | some g => (g false).field == [slot 0 goblin] && (g true).grave == [shock]
  | none => false
-- 対象を選ばなければ何も起きない
#guard match (board [⟨1, 0, shock, true, 0, 0, 0⟩] [slot 0 goblin, slot 1 goblin]).step? rules
    (.resolve true 0 0 true []) with
  | some g => (g false).field.length == 2
  | none => false
-- 巨大化：熊は 5/5 になり、ブロックした丘巨人（3/3）を破壊して残る。ターンの終わりに元に戻る
def grown : Option State :=
  (board [slot 0 bear, ⟨1, 0, growth, true, 0, 0, 0⟩] [slot 0 giant]).step? rules (.resolve true 1 0 true [] (some (true, 0)))
#guard match grown with
  | some g => g.atkOf rules [] (true, 0) (slot 0 bear) == 2 &&
      ((g true).field.head?.map fun sl => g.atkOf rules [] (true, 0) sl) == some 5
  | none => false
#guard match grown.bind (·.step? rules (.combat true [0] [(0, 0)] [])) with
  | some g => (g false).field.isEmpty && (g true).field.length == 1 && ((g true).field.head?.map (·.damage)) == some 3 &&
      ((g.mend true).field.head?.map (·.base)) == some (slot 0 bear)
  | none => false
-- 対抗呪文：相手のスタックの紅蓮地獄を、解決させずに墓地へ送る
#guard match (board [⟨1, 0, pyroclasm, true, 0, 0, 0⟩] [⟨1, 0, counterspell, true, 0, 0, 0⟩]).step? rules
    (.resolve false 0 0 true [] (some (true, 0))) with
  | some g => (g true).field.isEmpty && (g true).grave == [pyroclasm] && (g false).grave == [counterspell]
  | none => false
-- 飛行：風のドレイクの攻撃は、灰色熊ではブロックできず、到達を持つ巨大蜘蛛ならブロックできる
def flyer : Match := ⟨board [slot 0 drake] [slot 0 bear, slot 1 spider], { tp := true, count := 3 }⟩
#guard (Match.run rules flyer [.attack 0 none [], .pass, .pass, .block [(0, 0)] []]).isNone
#guard (Match.run rules flyer [.attack 0 none [], .pass, .pass, .block [(1, 0)] []]).isSome
-- 守備力が 0 になったクリーチャーは、状態の確認で破壊される
#guard match (board [{ slot 0 goblin with defBonus := -1 }] []).step? rules (.settle []) with
  | some g => (g true).field.isEmpty && (g true).grave == [goblin]
  | none => false
#guard match (board [slot 0 goblin] []).step? rules (.settle []) with
  | some g => (g true).field.length == 1
  | none => false

/-! ## インスタントとスタック -/

/-- 自分：山・山・丘巨人、手札に紅蓮地獄。相手：山・カープルーザンの森・ゴブリンの先兵、手札に稲妻と治癒の軟膏 -/
def duel : Match :=
  ⟨fun p => { deck := [mountain, mountain], hand := if p then [pyroclasm] else [bolt, salve], grave := [], life := 20,
              field := [slot 0 mountain, slot 1 (if p then mountain else karplusan), slot 2 (if p then giant else goblin)] },
   { tp := true, count := 3 }⟩

/-- 自分が紅蓮地獄を唱え（スタックに積まれる）、パスして優先権を渡し、相手が応答して稲妻を唱える -/
def respond : List TChoice := [.tap 0, .tap 1, .place 0 1 0 true ["赤", "赤"], .pass, .oppTap 0, .cast 0 1 0 true ["赤"]]

/-! ## 優先権（公理） -/

-- 優先権を持たないプレイヤーは動けない（最初はターンプレイヤーが持つ）
#guard (Match.run rules duel [.oppTap 0]).isNone
-- パスすると相手に移り、パスしたプレイヤーは動けない
#guard (Match.run rules duel [.pass, .tap 0]).isNone
#guard match Match.run rules duel [.pass] with
  | some m => m.turn.prio == false && m.turn.passes == 1
  | none => false
-- 両者が続けてパスしても、スタックが空で攻撃の途中でもなければ、何も起きずにターンプレイヤーに戻る
#guard match Match.run rules duel [.pass, .pass, .tap 0] with
  | some m => m.turn.prio == true && m.turn.passes == 0 && m.turn.pool == ["赤"]
  | none => false
-- 動いた本人が優先権を持ち続ける（紅蓮地獄を唱えたあとも自分が持つ）
#guard match Match.run rules duel (respond.take 3) with
  | some m => m.turn.prio == true
  | none => false
-- スタックがあるとき、両者がパスするまでは一番上も解決できない。パスしたら解決だけができる
#guard (Match.run rules duel (respond ++ [.resolve false 3 0 true])).isNone
#guard (Match.run rules duel (respond ++ [.pass, .pass, .tap 2])).isNone

#guard match Match.run rules duel respond with
  | some m => m.turn.stack.map (·.1) == [false, true] && m.turn.oppPool == [] && m.turn.spent == 3 && m.turn.made == 3
  | none => false
-- スタックが空でなければ、攻撃やソーサリー速度の動きはできない。一番上（稲妻）からしか解決できない
#guard (Match.run rules duel (respond.take 3 ++ [.attack 2 none []])).isNone
#guard (Match.run rules duel (respond ++ [.resolve true 3 0 true])).isNone
-- 稲妻を解決（自分に 3 点）、次に紅蓮地獄を解決：ゴブリンの先兵は破壊され、丘巨人は 2 点のダメージが残る
#guard match Match.run rules duel (respond ++ [.pass, .pass, .resolve false 3 0 true, .pass, .pass, .resolve true 3 0 true]) with
  | some m => (m.g true).life == 17 && (m.g true).field == [slot 0 mountain, slot 1 mountain, slot 2 giant 2] &&
      (m.g false).grave == [bolt, goblin] && m.turn.stack.isEmpty
  | none => false
-- ダメージはターンの終わりに消える
#guard match Match.run rules duel
    (respond ++ [.pass, .pass, .resolve false 3 0 true, .pass, .pass, .resolve true 3 0 true, .endTurn]) with
  | some m => (m.g true).field.all (·.damage == 0)
  | none => false
-- 相手のターンには、相手のマナで払う（持っていない色では払えない）
#guard (Match.run rules duel [.pass, .oppTap 0, .cast 0 1 0 true ["緑"]]).isNone
-- カープルーザンの森は、赤か緑を選んでマナを出す（ほかの色や、色を選ばないことはできない）
#guard match Match.run rules duel [.pass, .oppTap 1 "緑"] with
  | some m => m.turn.oppPool == ["緑"]
  | none => false
#guard (Match.run rules duel [.pass, .oppTap 1 "白"]).isNone
#guard (Match.run rules duel [.pass, .oppTap 1]).isNone
-- 攻撃の途中（ブロックの前）にもインスタントを置ける。ブロックはスタックが空になってから
#guard match Match.run rules duel [.attack 2 none [], .pass, .oppTap 0, .cast 0 1 0 true ["赤"], .pass, .pass] with
  | some m => m.turn.attackers.length == 1 && m.turn.stack.length == 1 &&
      (m.step? rules (.block [(2, 0)] [])).isNone
  | none => false

/-! ## 対戦の終わり -/

-- ライフが 0 になったら、それ以上動けない
#guard match Match.run rules { duel with g := duel.g.set false { duel.g false with life := 3 } }
    [.tap 0, .attack 2 none [], .pass, .pass, .block [] []] with
  | some m => (m.g false).life == 0 && Match.over rules m && (m.step? rules .endTurn).isNone
  | none => false
-- ライブラリーから引けなければ負け
#guard match Match.run rules { duel with g := duel.g.set false { duel.g false with deck := [] } } [.endTurn] with
  | some m => m.turn.decked == some false && (m.step? rules (.tap 0)).isNone
  | none => false

end CardGen.Mtg

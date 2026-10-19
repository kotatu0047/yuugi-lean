import CardGen.Sample

/-!
# MTG 風の見本

マナ・タップ・召喚酔い・ブロック（MTG 式の戦闘）を使う、MTG に似たゲームの見本。
マナは5色（白・青・黒・赤・緑）で、基本土地はそれぞれ1色のマナを出す。コストは「どの色でも払える分」と
「色の決まった分」に分かれる（灰色熊は 1 ＋ 緑）。カードの種類は土地・クリーチャー・ソーサリー・
エンチャントで、ソーサリーは「スタック」のゾーンに置いてから発動する（フィールド上には数えない）。

- デッキ（ライブラリー）40枚・初期手札7枚・ライフ20・1ターンに1枚引く（先攻の最初のターンは引かない）
- 土地は1ターンに1枚まで。土地をタップして1マナを出し、カードのコストを払って置く
- クリーチャーは召喚酔いがあり、攻撃するとタップする。タップしているクリーチャーは、持ち主の次のターンまで攻撃もブロックもできない
- 攻撃されたプレイヤーがブロックするクリーチャーを選ぶ。ブロックされたら、攻撃力（パワー）と守備力（タフネス）で
  互いにダメージを与え、守備力以上のダメージを受けた方を破壊する。ブロックされなければ攻撃力のダメージ

実際の MTG との違い（このプロトタイプで表せないもの）：2色以上から選べるマナ（多色の土地）、インスタントとスタックの応答、攻撃するクリーチャーを
まとめて宣言すること（ここでは1体ずつ攻撃する）、複数でのブロック、受けたダメージがターンの終わりまで残ること、
トランプルなどの能力、守備力（タフネス）を変える効果、デッキ切れの敗北。

同じ内容の JSON が `CardGen/mtg.json` にある。
-/

namespace CardGen.Mtg
open Lean Sample

def land : TypeName := "土地"
def creature : TypeName := "クリーチャー"
def sorcery : TypeName := "ソーサリー"
def enchantment : TypeName := "エンチャント"

def rules : Rules where
  cardTypes := [land, creature, sorcery, enchantment]
  deckSize := 40
  handSize := 7
  zones := [
    { name := "戦場", count := 1, capacity := .many, role := .plain, onField := true,
      admits := [land, creature, enchantment] },
    { name := "スタック", count := 1, capacity := .many, role := .plain, onField := false, admits := [sorcery] },
    { name := "ライブラリー", count := 1, capacity := .many, role := .deck, onField := false,
      admits := [land, creature, sorcery, enchantment] },
    { name := "墓地", count := 1, capacity := .many, role := .grave, onField := false,
      admits := [land, creature, sorcery, enchantment] }]
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

def mountain : Card := { name := "山", type := land, tags := [], effects := [], mana := 1, manaColor := "赤" }
def forest : Card := { name := "森", type := land, tags := [], effects := [], mana := 1, manaColor := "緑" }
def plains : Card := { name := "平地", type := land, tags := [], effects := [], mana := 1, manaColor := "白" }
def island : Card := { name := "島", type := land, tags := [], effects := [], mana := 1, manaColor := "青" }

def goblin : Card :=
  { name := "ゴブリンの先兵", type := creature, tags := ["赤", "ゴブリン"], effects := [], attack := 1, defense := 1,
    colorCost := ["赤"] }
def bear : Card :=
  { name := "灰色熊", type := creature, tags := ["緑", "熊"], effects := [], attack := 2, defense := 2,
    cost := 1, colorCost := ["緑"] }
def giant : Card :=
  { name := "丘巨人", type := creature, tags := ["赤", "巨人"], effects := [], attack := 3, defense := 3,
    cost := 3, colorCost := ["赤"] }
def knight : Card :=
  { name := "白騎士", type := creature, tags := ["白", "騎士"], effects := [], attack := 2, defense := 2,
    colorCost := ["白", "白"] }

def bolt : Card :=
  { name := "稲妻", type := sorcery, tags := ["赤"], effects := [.activated [.damage 3]], colorCost := ["赤"] }
def wrath : Card :=
  { name := "神の怒り", type := sorcery, tags := ["白"],
    effects := [.activated [.destroy (sel [creature] .both)]], cost := 2, colorCost := ["白", "白"] }
def unsummon : Card :=
  { name := "送還の波", type := sorcery, tags := ["青"],
    effects := [.activated [.bounce (sel [creature] .opp)]], cost := 3, colorCost := ["青"] }
def divination : Card :=
  { name := "予言", type := sorcery, tags := ["青"], effects := [.activated [.draw 2]], cost := 1, colorCost := ["青"] }
def salve : Card :=
  { name := "治癒の軟膏", type := sorcery, tags := ["白"], effects := [.activated [.heal 4]], colorCost := ["白"] }
def anthem : Card :=
  { name := "栄光の頌歌", type := enchantment, tags := ["白"],
    effects := [.boost (sel [creature] .self) 1], cost := 2, colorCost := ["白"] }
def silence : Card :=
  { name := "沈黙の結界", type := enchantment, tags := ["白"],
    effects := [.negate (sel [enchantment] .opp)], cost := 1, colorCost := ["白"] }

def game : Game where
  version := currentVersion
  rules := rules
  cards := [mountain, forest, plains, island, goblin, bear, giant, knight, bolt, wrath, unsummon, divination, salve, anthem,
            silence]

/-! ## 検査 -/

#guard game.WellFormed

-- `mtg.json` は見本と同じ内容（Unity のエディタが「見本（MTG 風）」で読み込む写しも同じ）
#guard_msgs in
#eval show IO Unit from do
  let s ← IO.FS.readFile "CardGen/mtg.json"
  match Game.parse s with
  | .ok g => unless g == game do throw (IO.userError "mtg.json が見本と違います")
  | .error e => throw (IO.userError e)
  let u ← IO.FS.readFile "unity/CardGenEditor/Assets/CardGenEditor/Resources/mtg.json"
  unless u == s do throw (IO.userError "Unity の Resources/mtg.json が CardGen/mtg.json と違います")

-- ★：土地は1ターンに1枚まで、タップしているカードは使えない、ブロックの★が報告に出る
#guard ((report (toJson game).compress).claims.map (·.text)).contains "「土地」を置けるのは、1ターンに 1 枚まで"

/-! ## 対戦 -/

/-- 手札7枚：山・山・ゴブリンの先兵・灰色熊・稲妻・山・森。そのあと引くのは山・灰色熊・…… -/
def deck : List Card :=
  [mountain, mountain, goblin, bear, bolt, mountain, forest] ++
  (List.range 33).map fun i => if i % 2 == 0 then mountain else bear

def m0 : Match := Match.start rules (fun _ => deck) true

/-- 1ターン目：山を置き、タップして赤マナを出し、それでゴブリンの先兵（赤）を置く -/
def turn1 : List TChoice := [.place 0 0 0 true, .tap 0, .place 1 0 0 true ["赤"]]

#guard match Match.run rules m0 turn1 with
  | some m => (m.g true).field.map (·.card.name) == ["山", "ゴブリンの先兵"] && m.turn.pool == []
  | none => false
-- 土地は1ターンに1枚まで。マナが足りなければ置けない（灰色熊は 1 ＋ 緑）
#guard (Match.run rules m0 [.place 0 0 0 true, .place 0 0 0 true]).isNone
#guard (Match.run rules m0 [.place 0 0 0 true, .tap 0, .place 2 0 0 true ["赤"]]).isNone
-- 色が違えば払えない：森を置いて緑マナを出しても、ゴブリンの先兵（赤）は置けない
#guard (Match.run rules m0 [.place 6 0 0 true, .tap 0, .place 2 0 0 true ["緑"]]).isNone
#guard (Match.run rules m0 [.place 6 0 0 true, .tap 0, .place 2 0 0 true ["赤"]]).isNone
-- 3ターン目に森を置けば、山と森で灰色熊（1 ＋ 緑）を置ける。どの色でも払える分は赤で払う
#guard match Match.run rules m0
    (turn1 ++ [.endTurn] ++ turn1 ++ [.endTurn, .place 4 0 0 true, .tap 0, .tap 2]) with
  | some m => m.turn.pool == ["赤", "緑"] && autoPay bear m.turn.pool == some ["緑", "赤"] &&
      autoPay giant m.turn.pool == none &&
      ((m.step? rules (.place 1 0 0 true ["緑", "赤"])).map fun m' => m'.turn.pool) == some []
  | none => false
-- 召喚酔い：置いたターンには攻撃できない
#guard (Match.run rules m0 (turn1 ++ [.attack 1 none []])).isNone

/-- 2ターン目（相手）：同じように山とゴブリンの先兵。3ターン目（自分）：ゴブリンの先兵で攻撃を宣言する -/
def toAttack : List TChoice := turn1 ++ [.endTurn] ++ turn1 ++ [.endTurn, .attack 1 none []]

-- 攻撃を宣言すると、相手がブロックを選ぶまで待つ（ほかの動きはできない）
#guard match Match.run rules m0 toAttack with
  | some m => m.turn.pending == some 1
  | none => false
#guard (Match.run rules m0 (toAttack ++ [.endTurn])).isNone
-- ブロックしなければ、攻撃力の 1 点のダメージ
#guard match Match.run rules m0 (toAttack ++ [.block none []]) with
  | some m => (m.g false).life == 19 && m.turn.pending == none
  | none => false
-- 相手のゴブリンの先兵でブロックすると、互いに 1 点のダメージで両方とも破壊される（プレイヤーへのダメージはない）
#guard match Match.run rules m0 (toAttack ++ [.block (some 1) []]) with
  | some m => (m.g true).field.length == 1 && (m.g false).field.length == 1 && (m.g false).life == 20 &&
      (m.g true).grave == [goblin] && (m.g false).grave == [goblin]
  | none => false
-- 戦闘できないカード（山）ではブロックできない
#guard (Match.run rules m0 (toAttack ++ [.block (some 0) []])).isNone
-- 攻撃したゴブリンの先兵はタップしたまま。相手のターンには、ブロックできない
#guard (Match.run rules m0 (toAttack ++ [.block none [], .endTurn, .attack 1 none [], .block (some 1) []])).isNone
#guard match Match.run rules m0 (toAttack ++ [.block none [], .endTurn, .attack 1 none [], .block none []]) with
  | some m => (m.g true).life == 19 && (m.g false).life == 19
  | none => false

/-- 熊（2/2）がゴブリンの先兵（1/1）にブロックされると、ゴブリンの先兵だけが破壊される -/
def bearVsGoblin : State := fun p =>
  { deck := [], hand := [], grave := [], life := 20,
    field := [⟨0, 0, if p then bear else goblin, true⟩] }

#guard match bearVsGoblin.step? rules (.attack true 0 (some 0) []) with
  | some g => (g true).field.length == 1 && (g false).field.isEmpty
  | none => false
-- 栄光の頌歌（自分のクリーチャーの攻撃力 +1）があっても、守備力（タフネス）は変わらない：
-- ゴブリンの先兵（2/1）が熊（2/2）にブロックされると、両方とも破壊される
def anthemGoblin : State := fun p =>
  if p then { bearVsGoblin p with field := [⟨0, 0, goblin, true⟩, ⟨0, 0, anthem, true⟩] }
  else { bearVsGoblin p with field := [⟨0, 0, bear, true⟩] }

#guard match anthemGoblin.step? rules (.attack true 0 (some 0) []) with
  | some g => (g true).field.map (·.card.name) == ["栄光の頌歌"] && (g false).field.isEmpty
  | none => false

end CardGen.Mtg

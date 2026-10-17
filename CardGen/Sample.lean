import CardGen.Negation

/-!
# 中間表現の見本

ユーザーの入力例のルール（初期手札5枚、デッキ40枚、モンスター・魔法・罠、ゾーン12マス）と、
プロトタイプで表せるカード6枚。同じ内容の JSON が `CardGen/sample.json` にある。
-/

namespace CardGen.Sample
open Lean

def monster : TypeName := "モンスター"
def spell : TypeName := "魔法"
def trap : TypeName := "罠"

def rules : Rules where
  cardTypes := [monster, spell, trap]
  deckSize := 40
  handSize := 5
  zones := [
    { name := "モンスターカードゾーン", count := 5, capacity := .one, role := .plain,
      onField := true, admits := [monster] },
    { name := "魔法罠ゾーン", count := 5, capacity := .one, role := .plain,
      onField := true, admits := [spell, trap] },
    { name := "デッキゾーン", count := 1, capacity := .many, role := .deck,
      onField := false, admits := [monster, spell, trap] },
    { name := "墓地ゾーン", count := 1, capacity := .many, role := .grave,
      onField := false, admits := [monster, spell, trap] }]

/-- 範囲の指定を短く書く -/
def sel (types : List TypeName) (side : Side) (faceUpOnly := false) (excludeSelf := false) :
    Selector :=
  { types, tags := [], side, faceUpOnly, excludeSelf }

def thunderbolt : Card :=
  { name := "サンダー・ボルト", type := spell, tags := [],
    effects := [.activated [.destroy (sel [monster] .opp)]] }

def featherDuster : Card :=
  { name := "ハーピィの羽根帚", type := spell, tags := [],
    effects := [.activated [.destroy (sel [spell, trap] .opp)]] }

def skillDrain : Card :=
  { name := "スキルドレイン", type := trap, tags := [],
    effects := [.negate (sel [monster] .both (faceUpOnly := true))] }

def royalDecree : Card :=
  { name := "王宮のお触れ", type := trap, tags := [],
    effects := [.negate (sel [trap] .both (faceUpOnly := true) (excludeSelf := true))] }

def jinzo : Card :=
  { name := "人造人間－サイコ・ショッカー", type := monster, tags := ["闇属性", "機械族"],
    effects := [.negate (sel [trap] .both (faceUpOnly := true))] }

/-- 装備の効果と特殊召喚の条件は、プロトタイプでは表せないので無効の効果だけ -/
def blooD : Card :=
  { name := "D－HERO Bloo－D", type := monster, tags := ["闇属性", "戦士族"],
    effects := [.negate (sel [monster] .opp (faceUpOnly := true))] }

def game : Game where
  version := currentVersion
  rules := rules
  cards := [thunderbolt, featherDuster, skillDrain, royalDecree, jinzo, blooD]

/-! ## 検査 -/

/-- 見本は中間表現として意味が通る -/
theorem game_wellFormed : game.WellFormed := by decide

-- JSON にして読み戻すと元に戻る
#guard match (fromJson? (toJson game) : Except String Game) with
  | .ok g => g == game
  | .error _ => false

-- `sample.json` は見本と同じ内容
#guard_msgs in
#eval show IO Unit from do
  let s ← IO.FS.readFile "CardGen/sample.json"
  match Game.parse s with
  | .ok g => unless g == game do throw (IO.userError "sample.json が見本と違います")
  | .error e => throw (IO.userError e)

/-! ## 範囲の指定の例 -/

def view (type : TypeName) (mine : Bool) (isSelf := false) : View :=
  { type, tags := [], mine, faceUp := true, isSelf }

-- お触れは自分以外の罠を無効にし、自分自身は無効にしない
#guard (sel [trap] .both true true).matches (view trap true (isSelf := true)) = false
#guard (sel [trap] .both true true).matches (view trap false) = true
-- Bloo－D は相手のモンスターだけを無効にする
#guard (sel [monster] .opp true).matches (view monster false) = true
#guard (sel [monster] .opp true).matches (view monster true) = false
-- ハーピィの羽根帚は裏側表示の魔法・罠も破壊する
#guard (sel [spell, trap] .opp).matches { view trap false with faceUp := false } = true
-- スキルドレインは裏側表示のモンスターには及ばない
#guard (sel [monster] .both true).matches { view monster false with faceUp := false } = false

/-! ## 形式の誤りの例 -/

/-- 入力を間違えたルールとカード -/
def broken : Game where
  version := currentVersion
  rules := { rules with
    handSize := 41
    zones := rules.zones.map fun z =>
      if z.role == .grave then { z with capacity := .one, admits := [monster] } else z }
  cards := [thunderbolt, { jinzo with type := "儀式モンスター" },
    { name := "空の魔法", type := spell, tags := [], effects := [.activated []] }]

/--
info: ルール：初期手札（41枚）がデッキの枚数（40枚）より多いです
ゾーン「墓地ゾーン」：デッキや墓地の役割のゾーンは「何枚でも」にしてください
ゾーン「墓地ゾーン」：デッキや墓地の役割のゾーンには、すべての種類のカードを置けるようにしてください
カード「人造人間－サイコ・ショッカー」：種類「儀式モンスター」はルールにありません
カード「空の魔法」：発動する効果に動きがありません
-/
#guard_msgs in
#eval IO.println ("\n".intercalate broken.check)

end CardGen.Sample

namespace CardGen.Sample

/-! ## 入力例から導く★ -/

/--
info: ゲーム開始時のデッキは各プレイヤー35枚 ← デッキの枚数（40枚）、初期手札（5枚）
ゲーム開始時の手札は各プレイヤー5枚 ← 初期手札（5枚）、デッキの枚数（40枚）
カードの総数は常に80枚 ← デッキの枚数（40枚）、共通ルール①（プレイヤーは自分と相手の2人）
自分のフィールド上のカードは最大10枚 ← ゾーン「モンスターカードゾーン」（5マス、1枚まで、置ける種類：モンスター）、ゾーン「魔法罠ゾーン」（5マス、1枚まで、置ける種類：魔法・罠）
フィールド全体のカードは最大20枚 ← ゾーン「モンスターカードゾーン」（5マス、1枚まで、置ける種類：モンスター）、ゾーン「魔法罠ゾーン」（5マス、1枚まで、置ける種類：魔法・罠）、共通ルール②（相手のフィールドは自分のフィールドを逆さまにした形）
自分のフィールド上のモンスターのカードは最大5枚 ← ゾーン「モンスターカードゾーン」（5マス、1枚まで、置ける種類：モンスター）
フィールド全体のモンスターのカードは最大10枚 ← ゾーン「モンスターカードゾーン」（5マス、1枚まで、置ける種類：モンスター）、共通ルール②（相手のフィールドは自分のフィールドを逆さまにした形）
自分のフィールド上の魔法のカードは最大5枚 ← ゾーン「魔法罠ゾーン」（5マス、1枚まで、置ける種類：魔法・罠）
フィールド全体の魔法のカードは最大10枚 ← ゾーン「魔法罠ゾーン」（5マス、1枚まで、置ける種類：魔法・罠）、共通ルール②（相手のフィールドは自分のフィールドを逆さまにした形）
自分のフィールド上の罠のカードは最大5枚 ← ゾーン「魔法罠ゾーン」（5マス、1枚まで、置ける種類：魔法・罠）
フィールド全体の罠のカードは最大10枚 ← ゾーン「魔法罠ゾーン」（5マス、1枚まで、置ける種類：魔法・罠）、共通ルール②（相手のフィールドは自分のフィールドを逆さまにした形）
-/
#guard_msgs in
#eval IO.println ("\n".intercalate ((derived rules).map fun c => s!"{c.text} ← {"、".intercalate c.grounds}"))

/-- 見本のルールの★は、どの対戦でも成り立つ -/
example (decks : PlayerId → List Card) (hd : ∀ p, (decks p).length = 40) :
    ∀ c ∈ derived rules, c.prop.Valid rules decks :=
  derived_valid rules decks hd

end CardGen.Sample

namespace CardGen.Sample

/-! ## 無効の関係の検査 -/

-- 見本の6枚：4すくみの4枚の間に循環がある（お触れ・Bloo－D は別の実体どうしで無効にし合える）
/--
info: CardGen.NegResult.cyclic [["スキルドレイン", "王宮のお触れ", "人造人間－サイコ・ショッカー", "D－HERO Bloo－D"]]
-/
#guard_msgs in
#eval checkNegation game.cards

/-- 魔法の効果を無効にするモンスター（循環のない例に使う） -/
def spellBreaker : Card :=
  { name := "魔法無効モンスター", type := monster, tags := [],
    effects := [.negate (sel [spell] .both (faceUpOnly := true))] }

/-- スキルドレインがモンスターを、モンスターが魔法を無効にするだけなら循環はない -/
def acyclicCards : List Card := [thunderbolt, skillDrain, spellBreaker]

#guard match checkNegation acyclicCards with | .proved => true | _ => false

/-- **この3枚だけが並ぶどの盤面でも、無効の判定は必ず止まり、結果は1通り** -/
theorem acyclic_settles (insts : List Inst) (hin : ∀ a ∈ insts, a.card ∈ acyclicCards) :
    let S := System.ofInsts insts
    WellFounded (fun g f => S.Step f g) ∧ (∃ f, S.Stable f) ∧
    ∀ f g, S.Stable f → S.Stable g → ∀ x < S.n, f x = g x :=
  negation_settles (rank := rankFn acyclicCards (computeRanks acyclicCards)) (by decide) insts hin

end CardGen.Sample

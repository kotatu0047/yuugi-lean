import CardGen.Report
import CardGen.Play

/-!
# 中間表現の見本

ユーザーの入力例のルール（初期手札5枚、デッキ40枚、モンスター・魔法・罠、ゾーン12マス、
ライフ8000、モンスターが戦闘する）と、プロトタイプで表せるカード13枚。同じ内容の JSON が `CardGen/sample.json` にある。
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
  life := 8000
  fighters := [monster]

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
    effects := [.negate (sel [trap] .both (faceUpOnly := true))], attack := 2400, defense := 1500 }

/-- 装備の効果と特殊召喚の条件は、プロトタイプでは表せないので無効の効果だけ -/
def blooD : Card :=
  { name := "D－HERO Bloo－D", type := monster, tags := ["闇属性", "戦士族"],
    effects := [.negate (sel [monster] .opp (faceUpOnly := true))], attack := 1900, defense := 600 }

/-- 相手のモンスターをすべて手札に戻す魔法 -/
def returnSpell : Card :=
  { name := "一斉送還", type := spell, tags := [],
    effects := [.activated [.bounce (sel [monster] .opp)]] }

/-- カードを2枚ドローする魔法 -/
def drawSpell : Card :=
  { name := "二枚引き", type := spell, tags := [],
    effects := [.activated [.draw 2]] }

/-- 効果を持たないモンスター -/
def blackMagician : Card :=
  { name := "ブラック・マジシャン", type := monster, tags := ["闇属性", "魔法使い族"], effects := [],
    attack := 2500, defense := 2100 }

/-- 自分のほかの闇属性モンスターの攻撃力を上げるモンスター（スキルドレインで無効になる） -/
def darkCommander : Card :=
  { name := "闇の指揮官", type := monster, tags := ["闇属性", "戦士族"],
    effects := [.boost { types := [monster], tags := ["闇属性"], side := .self, faceUpOnly := true,
                         excludeSelf := true } 300],
    attack := 1600, defense := 1000 }

/-- 自分の闇属性モンスターの攻撃力を上げる永続魔法（スキルドレインでは無効にならない） -/
def darkBlessing : Card :=
  { name := "闇の加護", type := spell, tags := [],
    effects := [.boost { types := [monster], tags := ["闇属性"], side := .self, faceUpOnly := true,
                         excludeSelf := false } 500] }

/-- 相手に500ダメージを与える魔法 -/
def fireball : Card :=
  { name := "ファイヤー・ボール", type := spell, tags := [], effects := [.activated [.damage 500]] }

/-- ライフを500回復する魔法 -/
def potion : Card :=
  { name := "レッド・ポーション", type := spell, tags := [], effects := [.activated [.heal 500]] }

def game : Game where
  version := currentVersion
  rules := rules
  cards := [thunderbolt, featherDuster, skillDrain, royalDecree, jinzo, blooD, returnSpell, drawSpell,
    blackMagician, darkCommander, darkBlessing, fireball, potion]

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
  -- Unity のエディタが「見本」で読み込む写しも同じ内容
  let u ← IO.FS.readFile "unity/CardGenEditor/Assets/CardGenEditor/Resources/sample.json"
  unless u == s do throw (IO.userError "Unity の Resources/sample.json が CardGen/sample.json と違います")

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
デッキは各プレイヤー最大35枚（増えない） ← デッキの枚数（40枚）、初期手札（5枚）、デッキにカードを戻す効果の部品がない
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

-- 見本の8枚：4すくみの4枚の間に循環がある（お触れ・Bloo－D は別の実体どうしで無効にし合える）
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

namespace CardGen.Sample

/-! ## 循環があるときの総当たり -/

-- 4すくみの盤面（スキルドレイン・お触れ・ショッカーが自分、Bloo－D が相手）：
-- 結果は1通りだが、選び方によって判定が回り続ける（yuugi-lean の quad_someEnd と同じ結論）
#guard analyzeBoard [⟨skillDrain, true, true⟩, ⟨royalDecree, true, true⟩, ⟨jinzo, true, true⟩,
  ⟨blooD, false, true⟩] == .someLoop

-- お触れどうし：互いに無効にし合い、結果が順番で変わる
#guard analyzeBoard [⟨royalDecree, true, true⟩, ⟨royalDecree, false, true⟩] == .multiStable

/-- 自分も含めてすべてのモンスターの効果を無効にするモンスター -/
def selfNegator : Card :=
  { name := "自分も無効にするモンスター", type := monster, tags := [],
    effects := [.negate (sel [monster] .both (faceUpOnly := true))] }

-- 自分自身を無効にする：どの状態も安定しない
#guard analyzeBoard [⟨selfNegator, true, true⟩] == .noStable

-- 検査ツールは、自分自身を無効にするカードを反例として報告する
#guard (negOut game.rules [selfNegator]).status == "counterexample"

/-! ## 適用の時刻つきの判定（OCG の手順） -/

/-- 4すくみ：スキルドレイン・お触れ・ショッカーが自分、Bloo－D が相手 -/
def quadBoard : List Inst :=
  [⟨skillDrain, true, true⟩, ⟨royalDecree, true, true⟩, ⟨jinzo, true, true⟩, ⟨blooD, false, true⟩]

-- Bloo－D 側（相手）のターンなら、どの状態から、どう選んでも止まり、結果は1通り
-- （yuugi-lean の quad_allEnd_any と同じ結論）。証明書の検査も通る
#guard ((TSys.ofInsts quadBoard).analyze false).verdict == .unique
#guard let S := TSys.ofInsts quadBoard; S.certified false (S.analyze false)
-- 結果は「スキルドレイン無効・お触れ有効・ショッカー無効・Bloo－D 有効」
#guard let r := (TSys.ofInsts quadBoard).analyze false; r.res.toList.all (·.2 == [false, true, false, true])
-- スキルドレイン側のターンでは、選び方によって回り続ける（quad_someEnd と同じ）
#guard ((TSys.ofInsts quadBoard).analyze true).verdict == .someLoop

-- 自分のスキルドレイン・ショッカーと、相手のお触れ・Bloo－D：自分のターンでは止まらない状態がある
-- （yuugi-lean の loopSrcs と同じ盤面）
#guard ((TSys.ofInsts [⟨skillDrain, true, true⟩, ⟨jinzo, true, true⟩, ⟨royalDecree, false, true⟩,
  ⟨blooD, false, true⟩]).analyze true).verdict == .cannotHalt

-- お触れどうし：先に適用された方が勝つので、結果は適用された順番だけで決まる
#guard ((TSys.ofInsts [⟨royalDecree, true, true⟩, ⟨royalDecree, false, true⟩]).analyze true).verdict == .byHistory

-- 自分自身を無効にするカード：止まる状態がない
#guard ((TSys.ofInsts [⟨selfNegator, true, true⟩]).analyze true).verdict == .noStable

-- 4すくみの4枚のまとまりは、上の止まらない盤面が見つかるので「反例あり」
#guard (negOut game.rules game.cards).status == "counterexample"

-- 容量：モンスターカードゾーンは5マスなので、モンスター6枚は置けない
#guard fitsZones game.rules (List.replicate 5 jinzo)
#guard !fitsZones game.rules (List.replicate 6 jinzo)

end CardGen.Sample

namespace CardGen.Sample

/-! ## 戦闘とライフ -/

/-- 自分：闇の指揮官・ブラック・マジシャン・闇の加護、相手：サイコ・ショッカー・裏側表示の Bloo－D -/
def battleState : State := fun p =>
  if p then { deck := [], hand := [], grave := [], life := 8000,
              field := [⟨0, darkCommander, true⟩, ⟨0, blackMagician, true⟩, ⟨1, darkBlessing, true⟩] }
  else { deck := [], hand := [], grave := [], life := 8000,
         field := [⟨0, jinzo, true⟩, ⟨0, blooD, false⟩] }

-- ブラック・マジシャンの攻撃力：2500 ＋ 指揮官 300 ＋ 加護 500
#guard battleState.atkOf rules [] (true, 1) ⟨0, blackMagician, true⟩ == 3300
-- 指揮官自身には指揮官の効果は及ばない：1600 ＋ 加護 500
#guard battleState.atkOf rules [] (true, 0) ⟨0, darkCommander, true⟩ == 2100
-- 指揮官の効果が無効（スキルドレインなど）なら 2500 ＋ 500
#guard battleState.atkOf rules [(true, 0)] (true, 1) ⟨0, blackMagician, true⟩ == 3000
-- サイコ・ショッカーは相手の加護の範囲外（「自分の」闇属性モンスター）：2400 のまま
#guard battleState.atkOf rules [] (false, 0) ⟨0, jinzo, true⟩ == 2400

-- ブラック・マジシャン（3300）でサイコ・ショッカー（2400）を攻撃：ショッカーは破壊され、相手は 900 のダメージ
#guard match battleState.step? rules (.attack true 1 (some 0) []) with
  | some g => (g false).life == 7100 && (g false).field.length == 1 && (g false).grave == [jinzo]
  | none => false
-- 指揮官（2100）でショッカー（2400）を攻撃：指揮官が破壊され、自分が 300 のダメージ
#guard match battleState.step? rules (.attack true 0 (some 0) []) with
  | some g => (g true).life == 7700 && (g true).grave == [darkCommander]
  | none => false
-- 裏側表示の Bloo－D（守備力 600）は守備力で受ける：破壊されるがダメージはない
#guard match battleState.step? rules (.attack true 0 (some 1) []) with
  | some g => (g false).life == 8000 && (g false).grave == [blooD]
  | none => false
-- 相手に戦闘できるカードがあるので直接攻撃はできない。魔法（加護）では攻撃できない
#guard (battleState.step? rules (.attack true 1 none [])).isNone
#guard (battleState.step? rules (.attack true 2 (some 0) [])).isNone

-- ファイヤー・ボールのダメージはライフ 0 で止まる
#guard ((battleState.set false { battleState false with life := 300 }).applyAction rules true (.damage 500) false).life == 0

-- 見本には回復の魔法があるので、ライフの上限の★はない。回復の魔法を除けば★「ライフは最大8000」が出る
#guard (gameClaims game).isEmpty
#guard (gameClaims { game with cards := game.cards.filter (· != potion) }).map (·.prop) == [.lifeMax 8000]

-- 攻撃力と無効の衝突：スキルドレイン（4すくみの循環の中）は闇の指揮官を無効にしうるので「プレイヤーの選択」
#guard (attackClaim game.cards).map (·.status) == some "choice"
-- 循環がなければ、攻撃力はどの盤面でも1通り
#guard (attackClaim [skillDrain, darkCommander, blackMagician]).map (·.status) == some "proved"
-- 攻撃力の変化を持つカードがなければ出さない
#guard (attackClaim [skillDrain, jinzo]).isNone

end CardGen.Sample

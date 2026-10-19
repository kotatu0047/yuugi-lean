import Lean.Data.Json

/-!
# カードゲームジェネレーターの中間表現

ビジュアルエディタが出力し、Lean の検査ツールと C# のゲームエンジンの両方が読む形式。
JSON との相互変換は Lean の自動導出による（`Option` 以外のフィールドはすべて必須）。

全ユーザー共通の前提（中間表現には書かない）:
- プレイヤーは自分と相手の2人
- 相手のフィールドは自分のフィールドを逆さまにした形（ゾーンの定義は1人分だけ書く）
- 優先権：優先権を持つプレイヤーだけが動ける。動いた本人が持ち続け、パスすると相手に移る。両者が続けてパスしたら、
  スタックの一番上を解決するか、攻撃の途中ならブロックに進み、どちらでもなければ何も起きない。どのあとも
  ターンプレイヤーに戻る（ターンのあるモデル `CardGen/Turn.lean` の `Match.step?`）

プロトタイプで表せる効果は、盤面の制約を守る動きだけに絞る：
- 発動して、条件に合うカードをすべて破壊する（サンダーボルト、ハーピィの羽根帚）・手札に戻す・
  決まった枚数ドローする
- 表側表示で存在する限り、条件に合うカードの効果を無効にする（スキルドレイン、王宮のお触れ など）
- 発動して、相手にダメージを与える・自分のライフを回復する
- 発動して、条件に合う戦闘できるカードすべてにダメージを与える（守備力以上のダメージを受けたカードは破壊される）
- 表側表示で存在する限り、条件に合うカードの攻撃力・守備力を上げる・下げる（無効にされていれば効かない）

版 2 で、ライフと戦闘（ルールの `life`・`fighters`、カードの `attack`・`defense`）を加えた。
版 3 で、ターンのルールを加えた。版 4 で、マスの位置（ゾーンの `cells`）と、範囲の指定の
マスの関係（`near`：隣・同じ縦列）を加えた。版 5 で、マナとタップ（カードの `cost`・`mana`）、
1ターンに置ける枚数の上限（`placeLimits`）、攻撃でタップすること（`attackTaps`）、
召喚酔い（`summoningSickness`）、MTG 式の戦闘（`blocking`）を加えた。版 6 で、色のマナ（ルールの `manaColors`、
カードの `colorCost`・`manaColor`）を加えた。版 7 で、タグの集合（`tagSets`）を加えた。版 8 で、
インスタント（ルールの `instants`）とスタック（`stack`）、カードへのダメージ（動きの `strike`）、守備力の変化
（効果の `toughen`）、2色以上から選べるマナ（カードの `manaChoice`）、トランプル（カードの `trample`）を加えた。
版 9 で、対象を1つ選ぶ範囲（範囲の指定の `target`）、ターンの終わりまでの攻撃力・守備力の変化（動きの `pump`）、
呪文を打ち消す動き（`counter`）、飛行と到達（カードの `flying`・`reach`）を加えた。

マスの並びは、縦と横の2本の序列で表す。盤面全体（2人分）は `gridSize`×`gridSize`（49×49。
前提の「最大 50×50」に収まり、中心のマスがあるように奇数にした）のマス目で、マスは（列, 行）で表し、
使うのは大小の比較と「1つ隣」だけ（距離や角度は使わない）。ゾーンのマスの位置は1人分
（`true` のプレイヤー）だけ書き、相手のマスは中心のマス（24, 24）について点対称の位置にある。
遊戯王は、このマス目の中央の一部（5列×4行）だけを使う。

ルールの数値を変える効果や、カードの種類を変える効果（「〜扱い」）は、表す手段を用意しない。
-/

namespace CardGen
open Lean

/-- カードの種類の名前。ルールの `cardTypes` で定義する（例：モンスター、魔法、罠） -/
abbrev TypeName := String

/-- マスの容量 -/
inductive Capacity
  | one   -- 1枚まで（モンスターカードゾーン、魔法罠ゾーン）
  | many  -- 何枚でも（デッキ、墓地）
deriving Repr, DecidableEq, FromJson, ToJson

/-- ゾーンの役割。ゲームの手順が使うゾーンを示す -/
inductive ZoneRole
  | deck   -- ゲーム開始時にデッキを置き、ドローするゾーン
  | grave  -- 破壊されたカードが送られるゾーン
  | plain  -- それ以外
deriving Repr, DecidableEq, FromJson, ToJson

/-- 盤面全体の縦と横のマスの数（2人分） -/
def gridSize : Nat := 49

/-- 盤面のマス目の位置（列, 行）。どちらも `gridSize` 未満 -/
structure Cell where
  col : Nat
  row : Nat
deriving Repr, DecidableEq, FromJson, ToJson

/-- 盤面の中心について点対称の位置（相手のマス） -/
def Cell.flip (c : Cell) : Cell := ⟨gridSize - 1 - c.col, gridSize - 1 - c.row⟩

/-- 隣り合う：列か行のどちらかが同じで、もう一方が1つ違う -/
def Cell.adjacent (a b : Cell) : Bool :=
  (a.col == b.col && (a.row + 1 == b.row || b.row + 1 == a.row)) ||
  (a.row == b.row && (a.col + 1 == b.col || b.col + 1 == a.col))

/-- ゾーンの定義（1人分） -/
structure Zone where
  name : String
  /-- 1人あたりのマスの数 -/
  count : Nat
  capacity : Capacity
  role : ZoneRole
  /-- 「フィールド上」に数えるか（デッキ・墓地は普通 false） -/
  onField : Bool
  /-- 置けるカードの種類 -/
  admits : List TypeName
  /-- マスの位置（`true` のプレイヤーの側。`count` 個）。空ならマス目の上にないゾーン -/
  cells : List Cell := []
deriving Repr, DecidableEq, FromJson, ToJson

/-- 1ターンに置ける枚数の上限（例：土地は1ターンに1枚） -/
structure PlaceLimit where
  /-- 対象のカードの種類（このどれか） -/
  types : List TypeName
  count : Nat
deriving Repr, DecidableEq, FromJson, ToJson

/-- タグの集合（例：属性＝闇属性・光属性、種族＝戦士族・機械族） -/
structure TagSet where
  name : String
  values : List String
deriving Repr, DecidableEq, FromJson, ToJson

/-- ゲームのルール -/
structure Rules where
  cardTypes : List TypeName
  /-- 1人あたりのデッキの枚数 -/
  deckSize : Nat
  /-- 初期手札の枚数 -/
  handSize : Nat
  zones : List Zone
  /-- 初期ライフ -/
  life : Nat := 0
  /-- 戦闘できる（攻撃する・攻撃される）カードの種類。空なら戦闘はない -/
  fighters : List TypeName := []
  /-- 1ターンに置ける、戦闘できる種類のカードの枚数（通常召喚の回数）。0 なら制限なし -/
  summonsPerTurn : Nat := 1
  /-- ターンの最初に引く枚数 -/
  drawPerTurn : Nat := 1
  /-- 先攻の最初のターンにも引くか -/
  firstTurnDraw : Bool := false
  /-- 先攻の最初のターンにも攻撃できるか -/
  firstTurnAttack : Bool := false
  /-- 1ターンに置ける枚数の上限（種類ごと） -/
  placeLimits : List PlaceLimit := []
  /-- 攻撃するとタップする（タップしているカードは攻撃できない） -/
  attackTaps : Bool := false
  /-- 置いたターンには、戦闘できるカードで攻撃したりマナを出したりできない（召喚酔い） -/
  summoningSickness : Bool := false
  /-- MTG 式の戦闘：攻撃されたプレイヤーが、ブロックするカードを選ぶ（選ばなければ直接のダメージ）。
  ブロックされたら、攻撃力（パワー）と守備力（タフネス）で互いにダメージを与え、守備力以上のダメージを受けた方を破壊する -/
  blocking : Bool := false
  /-- マナの色（例：白・青・黒・赤・緑）。空なら色のマナは使わない -/
  manaColors : List String := []
  /-- タグの集合。空でなければ、カードと範囲の指定のタグはどれかの集合の値 -/
  tagSets : List TagSet := []
  /-- いつでも置ける種類（インスタント）。相手のターンや、攻撃・スタックへの応答としても置ける -/
  instants : List TypeName := []
  /-- スタック：「フィールド上」でないゾーンに置いた、発動する効果を持つカード（呪文）は、後に置いたものから解決する。
  スタックが空でなければ、インスタント以外は置けず、攻撃・ブロック・ターン終了もできない -/
  stack : Bool := false
  /-- 手札の上限。ターンプレイヤーは、手札がこの枚数を超えていればターンを終えられず、超えた分を選んで墓地へ捨てる。0 なら上限なし -/
  handLimit : Nat := 0
deriving Repr, DecidableEq, FromJson, ToJson

/-- 効果の持ち主から見た陣営 -/
inductive Side
  | self  -- 効果の持ち主がコントロールするカード
  | opp   -- 相手がコントロールするカード
  | both
deriving Repr, DecidableEq, FromJson, ToJson

/-- 効果を持つカードのマスとの関係 -/
inductive Near
  | any         -- 条件なし
  | adjacent    -- 隣のマス
  | sameColumn  -- 同じ縦列（相手の側も含む。自分自身も同じ縦列）
deriving Repr, DecidableEq, FromJson, ToJson

/-- 範囲の指定。フィールド上のカードのうち、すべての条件に合うものを選ぶ -/
structure Selector where
  /-- カードの種類（このどれか） -/
  types : List TypeName
  /-- タグ（属性・種族など。このすべてを持つ。空なら条件なし） -/
  tags : List String
  side : Side
  /-- 表側表示のカードだけを選ぶか -/
  faceUpOnly : Bool
  /-- このカード自身を除くか -/
  excludeSelf : Bool
  /-- 効果を持つカードのマスとの関係（どちらかがマス目の上になければ、関係は成り立たない） -/
  near : Near := .any
  /-- 対象を1つ選ぶ（解決するときに、範囲に合うカードを1枚選び、そのカードだけに行う。永続効果の範囲には使えない） -/
  target : Bool := false
deriving Repr, DecidableEq, FromJson, ToJson

/-- 効果が解決したときの動き -/
inductive Action
  /-- 範囲に合うカードをすべて破壊し、持ち主の墓地へ送る -/
  | destroy (target : Selector)
  /-- 範囲に合うカードをすべて持ち主の手札に戻す -/
  | bounce (target : Selector)
  /-- 発動したプレイヤーがデッキからカードを `count` 枚引く（デッキが足りなければある分だけ） -/
  | draw (count : Nat)
  /-- 相手に `amount` のダメージを与える -/
  | damage (amount : Nat)
  /-- 発動したプレイヤーのライフを `amount` 回復する -/
  | heal (amount : Nat)
  /-- 範囲に合う、戦闘できるカードすべてに `amount` のダメージを与える（ダメージはターンの終わりまで残り、
  守備力以上のダメージを受けたカードは破壊される） -/
  | strike (target : Selector) (amount : Nat)
  /-- 範囲に合う、戦闘できるカードすべての攻撃力・守備力を、ターンの終わりまで変える（例：巨大化）。
  守備力が受けているダメージ以下になったカードは破壊される -/
  | pump (target : Selector) (attack : Int) (defense : Int)
  /-- 範囲に合う、「フィールド上」でないゾーンのカード（スタックにある呪文など）を、解決させずに墓地へ送る（打ち消す） -/
  | counter (target : Selector)
deriving Repr, DecidableEq, FromJson, ToJson

/-- カードの効果 -/
inductive Effect
  /-- 発動し、解決したときに動きを順に行う -/
  | activated (actions : List Action)
  /-- 表側表示でフィールド上に存在する限り、範囲に合うカードの効果を無効にする -/
  | negate (target : Selector)
  /-- 表側表示でフィールド上に存在する限り、範囲に合うカードの攻撃力を `amount` 変える（負なら下げる） -/
  | boost (target : Selector) (amount : Int)
  /-- 表側表示でフィールド上に存在する限り、範囲に合うカードの守備力を `amount` 変える（負なら下げる） -/
  | toughen (target : Selector) (amount : Int)
deriving Repr, DecidableEq, FromJson, ToJson

/-- カードの定義 -/
structure Card where
  name : String
  type : TypeName
  tags : List String
  effects : List Effect
  /-- 攻撃力（戦闘できる種類のカードだけが使う） -/
  attack : Nat := 0
  /-- 守備力（裏側表示で攻撃されたときに使う） -/
  defense : Nat := 0
  /-- 置くのに支払うマナのうち、どの色でも払える分 -/
  cost : Nat := 0
  /-- 置くのに支払うマナのうち、色の決まった分（例：`["赤", "赤"]`）。色はルールの `manaColors` のどれか -/
  colorCost : List String := []
  /-- タップすると出るマナの量 -/
  mana : Nat := 0
  /-- タップすると出るマナの色（`""` なら無色） -/
  manaColor : String := ""
  /-- タップするときに選べるマナの色（2色以上の土地。空でなければ `manaColor` は使わない） -/
  manaChoice : List String := []
  /-- トランプル（MTG 式の戦闘で、ブロックしたカードを破壊できるだけのダメージを与え、残りを相手に与える） -/
  trample : Bool := false
  /-- 飛行（MTG 式の戦闘で、飛行か到達を持つカードでしかブロックできない） -/
  flying : Bool := false
  /-- 到達（飛行を持つカードもブロックできる） -/
  reach : Bool := false
deriving Repr, DecidableEq, FromJson, ToJson

instance : Inhabited Card := ⟨{ name := "", type := "", tags := [], effects := [] }⟩

/-- エディタが出力する中間表現の全体 -/
structure Game where
  /-- 中間表現の形式の版。互換性のない変更で増やす -/
  version : Nat
  rules : Rules
  cards : List Card
deriving Repr, DecidableEq, FromJson, ToJson

/-- 現在の形式の版 -/
def currentVersion : Nat := 10

/-! ## 範囲の指定の意味

C# 側も同じ意味で実装し、差分テストで照合する。 -/

/-- 範囲を判定するときに見る、フィールド上のカード1枚の情報（効果の持ち主から見たもの） -/
structure View where
  type : TypeName
  tags : List String
  /-- 効果の持ち主がコントロールしているか -/
  mine : Bool
  faceUp : Bool
  /-- 効果を持つカード自身か -/
  isSelf : Bool
  /-- 効果を持つカードの隣のマスにあるか -/
  adjacent : Bool := false
  /-- 効果を持つカードと同じ縦列にあるか -/
  sameColumn : Bool := false
  /-- 解決するときに選んだ対象か -/
  isTarget : Bool := false
deriving Repr, DecidableEq

def Side.matches : Side → Bool → Bool
  | .self, mine => mine
  | .opp, mine => !mine
  | .both, _ => true

def Near.matches : Near → View → Bool
  | .any, _ => true
  | .adjacent, v => v.adjacent
  | .sameColumn, v => v.sameColumn

def Selector.matches (s : Selector) (v : View) : Bool :=
  s.types.contains v.type && s.tags.all v.tags.contains && s.side.matches v.mine &&
    (!s.faceUpOnly || v.faceUp) && !(s.excludeSelf && v.isSelf) && s.near.matches v && (!s.target || v.isTarget)

/-! ## 形式の検査

中間表現として意味が通るかを調べ、問題をすべて日本語で返す。空なら `WellFormed`。
-/

/-- リストの重複した要素 -/
def dups [BEq α] (l : List α) : List α :=
  (l.filter fun a => l.count a > 1).eraseDups

/-- タグの集合の値すべて -/
def Rules.allTags (r : Rules) : List String := r.tagSets.flatMap (·.values)

/-- タグの集合があるのに、どの集合にもないタグ -/
def Rules.unknownTags (r : Rules) (tags : List String) : List String :=
  if r.tagSets.isEmpty then [] else (tags.filter (!r.allTags.contains ·)).eraseDups

namespace Selector
def check (r : Rules) (where_ : String) (s : Selector) : List String :=
  (if s.types.isEmpty then [s!"{where_}：範囲のカードの種類が空です"] else []) ++
  (s.types.filter (!r.cardTypes.contains ·)).map
    (s!"{where_}：範囲のカードの種類「{·}」はルールにありません") ++
  (r.unknownTags s.tags).map (s!"{where_}：範囲のタグ「{·}」はどのタグの集合にもありません")
end Selector

def Action.check (r : Rules) (where_ : String) : Action → List String
  | .destroy s => s.check r s!"{where_}の破壊"
  | .bounce s => s.check r s!"{where_}の手札に戻す動き"
  | .draw n => if n = 0 then [s!"{where_}：ドローの枚数が0です"] else []
  | .damage n => if n = 0 then [s!"{where_}：ダメージが0です"] else []
  | .heal n => if n = 0 then [s!"{where_}：回復する量が0です"] else []
  | .strike s n => s.check r s!"{where_}のカードへのダメージ" ++
      (if n = 0 then [s!"{where_}：カードへのダメージが0です"] else []) ++
      (if s.types.any r.fighters.contains then [] else
        [s!"{where_}：カードへのダメージの範囲に、戦闘できる種類のカードがありません"])
  | .pump s a d => s.check r s!"{where_}のターンの終わりまでの変化" ++
      (if a = 0 ∧ d = 0 then [s!"{where_}：ターンの終わりまでの変化が攻撃力・守備力とも0です"] else []) ++
      (if s.types.any r.fighters.contains then [] else
        [s!"{where_}：ターンの終わりまでの変化の範囲に、戦闘できる種類のカードがありません"])
  | .counter s => s.check r s!"{where_}の打ち消し" ++
      (if s.types.any (fun t => r.zones.any fun z => z.role == .plain && !z.onField && z.admits.contains t) then [] else
        [s!"{where_}：打ち消す範囲の種類を、「フィールド上」でないゾーンに置けません"])

/-- 永続効果の範囲で対象を選ぼうとしていれば誤り -/
def Selector.noTarget (where_ : String) (s : Selector) : List String :=
  if s.target then [s!"{where_}：永続効果の範囲では、対象を選べません"] else []

def Effect.check (r : Rules) (where_ : String) : Effect → List String
  | .activated as => (if as.isEmpty then [s!"{where_}：発動する効果に動きがありません"] else []) ++
      as.flatMap (·.check r where_)
  | .negate s => s.check r s!"{where_}の無効" ++ s.noTarget s!"{where_}の無効"
  | .boost s n => s.check r s!"{where_}の攻撃力の変化" ++ s.noTarget s!"{where_}の攻撃力の変化" ++
      (if n = 0 then [s!"{where_}：攻撃力の変化が0です"] else []) ++
      (if s.types.any r.fighters.contains then [] else
        [s!"{where_}：攻撃力を変える範囲に、戦闘できる種類のカードがありません"])
  | .toughen s n => s.check r s!"{where_}の守備力の変化" ++ s.noTarget s!"{where_}の守備力の変化" ++
      (if n = 0 then [s!"{where_}：守備力の変化が0です"] else []) ++
      (if s.types.any r.fighters.contains then [] else
        [s!"{where_}：守備力を変える範囲に、戦闘できる種類のカードがありません"])

def Card.check (r : Rules) (c : Card) : List String :=
  (if r.cardTypes.contains c.type then [] else
    [s!"カード「{c.name}」：種類「{c.type}」はルールにありません"]) ++
  (r.unknownTags c.tags).map (s!"カード「{c.name}」：タグ「{·}」はどのタグの集合にもありません") ++
  (c.colorCost.eraseDups.filter (!r.manaColors.contains ·)).map
    (s!"カード「{c.name}」：コストの色「{·}」はルールのマナの色にありません") ++
  (if c.manaColor != "" && !r.manaColors.contains c.manaColor then
    [s!"カード「{c.name}」：出るマナの色「{c.manaColor}」はルールのマナの色にありません"] else []) ++
  (if c.manaColor != "" && c.mana = 0 then
    [s!"カード「{c.name}」：マナの色があるのに、出るマナの量が0です"] else []) ++
  (c.manaChoice.eraseDups.filter (!r.manaColors.contains ·)).map
    (s!"カード「{c.name}」：選べるマナの色「{·}」はルールのマナの色にありません") ++
  (dups c.manaChoice).map (s!"カード「{c.name}」：選べるマナの色「{·}」が重複しています") ++
  (if !c.manaChoice.isEmpty && c.manaColor != "" then
    [s!"カード「{c.name}」：マナの色と、選べるマナの色の両方があります"] else []) ++
  (if !c.manaChoice.isEmpty && c.mana = 0 then
    [s!"カード「{c.name}」：選べるマナの色があるのに、出るマナの量が0です"] else []) ++
  c.effects.flatMap (·.check r s!"カード「{c.name}」")

def Zone.check (r : Rules) (z : Zone) : List String :=
  let w := s!"ゾーン「{z.name}」"
  (if z.count = 0 then [s!"{w}：マスの数が0です"] else []) ++
  (if z.admits.isEmpty then [s!"{w}：置けるカードの種類が空です"] else []) ++
  (z.admits.filter (!r.cardTypes.contains ·)).map (s!"{w}：カードの種類「{·}」はルールにありません") ++
  (if z.role != .plain && z.capacity != .many then
    [s!"{w}：デッキや墓地の役割のゾーンは「何枚でも」にしてください"] else []) ++
  (if z.role != .plain && z.count != 1 then
    [s!"{w}：デッキや墓地の役割のゾーンはマスを1つにしてください"] else []) ++
  (if z.role != .plain && z.onField then
    [s!"{w}：デッキや墓地の役割のゾーンは「フィールド上」に数えないでください"] else []) ++
  (if z.role != .plain && r.cardTypes.any (!z.admits.contains ·) then
    [s!"{w}：デッキや墓地の役割のゾーンには、すべての種類のカードを置けるようにしてください"] else []) ++
  (if z.role != .plain && !z.cells.isEmpty then
    [s!"{w}：デッキや墓地の役割のゾーンにはマスの位置を付けないでください"] else []) ++
  (if !z.cells.isEmpty && z.cells.length != z.count then
    [s!"{w}：マスの位置の数（{z.cells.length}）がマスの数（{z.count}）と違います"] else []) ++
  (z.cells.filter (fun c => !(c.col < gridSize && c.row < gridSize))).map
    (fun c => s!"{w}：マス（{c.col}, {c.row}）が盤面（{gridSize}×{gridSize}）の外です")

/-- 2人分のマスの位置すべて（盤面の外のマスは除く。それは `Zone.check` が誤りにする） -/
def Rules.allCells (r : Rules) : List Cell :=
  let mine := (r.zones.flatMap (·.cells)).filter fun c => c.col < gridSize && c.row < gridSize
  mine ++ mine.map Cell.flip

def Rules.check (r : Rules) : List String :=
  (if r.cardTypes.isEmpty then ["ルール：カードの種類が空です"] else []) ++
  (dups r.cardTypes).map (s!"ルール：カードの種類「{·}」が重複しています") ++
  (if r.handSize > r.deckSize then
    [s!"ルール：初期手札（{r.handSize}枚）がデッキの枚数（{r.deckSize}枚）より多いです"] else []) ++
  (dups (r.zones.map (·.name))).map (s!"ルール：ゾーン「{·}」が重複しています") ++
  (match (r.zones.filter (·.role == .deck)).length with
    | 1 => [] | n => [s!"ルール：デッキの役割のゾーンがちょうど1つ必要です（{n}個あります）"]) ++
  (match (r.zones.filter (·.role == .grave)).length with
    | 1 => [] | n => [s!"ルール：墓地の役割のゾーンがちょうど1つ必要です（{n}個あります）"]) ++
  r.zones.flatMap (·.check r) ++
  (dups r.allCells).map (fun c => s!"ルール：マス（{c.col}, {c.row}）が重なっています（相手の側のマスも含む）") ++
  (r.fighters.filter (!r.cardTypes.contains ·)).map (s!"ルール：戦闘できる種類「{·}」はカードの種類にありません") ++
  (if !r.fighters.isEmpty && r.life = 0 then ["ルール：戦闘できる種類があるのに、初期ライフが0です"] else []) ++
  (dups r.manaColors).map (s!"ルール：マナの色「{·}」が重複しています") ++
  (dups (r.tagSets.map (·.name))).map (s!"ルール：タグの集合「{·}」が重複しています") ++
  (if r.tagSets.any (·.name.isEmpty) then ["ルール：タグの集合の名前が空です"] else []) ++
  r.tagSets.flatMap (fun t => (dups t.values).map (s!"ルール：タグの集合「{t.name}」で「{·}」が重複しています")) ++
  (if r.manaColors.contains "" then ["ルール：マナの色に空の名前があります"] else []) ++
  (r.instants.filter (!r.cardTypes.contains ·)).map (s!"ルール：いつでも置ける種類「{·}」はカードの種類にありません") ++
  r.placeLimits.flatMap fun l =>
    (if l.types.isEmpty then ["ルール：置ける枚数の上限の、カードの種類が空です"] else []) ++
    (l.types.filter (!r.cardTypes.contains ·)).map (s!"ルール：置ける枚数の上限の種類「{·}」はカードの種類にありません") ++
    (if l.count = 0 then [s!"ルール：「{"・".intercalate l.types}」を置ける枚数の上限が0です"] else [])

def Game.check (g : Game) : List String :=
  (if g.version = currentVersion then [] else
    [s!"中間表現の版 {g.version} には対応していません（対応は {currentVersion}）"]) ++
  g.rules.check ++
  (dups (g.cards.map (·.name))).map (s!"カード「{·}」が重複しています") ++
  g.cards.flatMap (·.check g.rules)

/-- 中間表現として意味が通る -/
def Game.WellFormed (g : Game) : Prop := g.check = []

instance (g : Game) : Decidable g.WellFormed := inferInstanceAs (Decidable (_ = _))

/-- JSON の文字列を読み、形式を検査する -/
def Game.parse (s : String) : Except String Game := do
  let g : Game ← fromJson? (← Json.parse s)
  match g.check with
  | [] => pure g
  | es => throw ("\n".intercalate es)

end CardGen

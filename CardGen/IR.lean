import Lean.Data.Json

/-!
# カードゲームジェネレーターの中間表現

ビジュアルエディタが出力し、Lean の検査ツールと C# のゲームエンジンの両方が読む形式。
JSON との相互変換は Lean の自動導出による（`Option` 以外のフィールドはすべて必須）。

全ユーザー共通の前提（中間表現には書かない）:
- プレイヤーは自分と相手の2人
- 相手のフィールドは自分のフィールドを逆さまにした形（ゾーンの定義は1人分だけ書く）

プロトタイプで表せる効果は、盤面の制約を守る動きだけに絞る：
- 発動して、条件に合うカードをすべて破壊する（サンダーボルト、ハーピィの羽根帚）・手札に戻す・
  決まった枚数ドローする
- 表側表示で存在する限り、条件に合うカードの効果を無効にする（スキルドレイン、王宮のお触れ など）

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
deriving Repr, DecidableEq, FromJson, ToJson

/-- ゲームのルール -/
structure Rules where
  cardTypes : List TypeName
  /-- 1人あたりのデッキの枚数 -/
  deckSize : Nat
  /-- 初期手札の枚数 -/
  handSize : Nat
  zones : List Zone
deriving Repr, DecidableEq, FromJson, ToJson

/-- 効果の持ち主から見た陣営 -/
inductive Side
  | self  -- 効果の持ち主がコントロールするカード
  | opp   -- 相手がコントロールするカード
  | both
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
deriving Repr, DecidableEq, FromJson, ToJson

/-- 効果が解決したときの動き -/
inductive Action
  /-- 範囲に合うカードをすべて破壊し、持ち主の墓地へ送る -/
  | destroy (target : Selector)
  /-- 範囲に合うカードをすべて持ち主の手札に戻す -/
  | bounce (target : Selector)
  /-- 発動したプレイヤーがデッキからカードを `count` 枚引く（デッキが足りなければある分だけ） -/
  | draw (count : Nat)
deriving Repr, DecidableEq, FromJson, ToJson

/-- カードの効果 -/
inductive Effect
  /-- 発動し、解決したときに動きを順に行う -/
  | activated (actions : List Action)
  /-- 表側表示でフィールド上に存在する限り、範囲に合うカードの効果を無効にする -/
  | negate (target : Selector)
deriving Repr, DecidableEq, FromJson, ToJson

/-- カードの定義 -/
structure Card where
  name : String
  type : TypeName
  tags : List String
  effects : List Effect
deriving Repr, DecidableEq, FromJson, ToJson

instance : Inhabited Card := ⟨⟨"", "", [], []⟩⟩

/-- エディタが出力する中間表現の全体 -/
structure Game where
  /-- 中間表現の形式の版。互換性のない変更で増やす -/
  version : Nat
  rules : Rules
  cards : List Card
deriving Repr, DecidableEq, FromJson, ToJson

/-- 現在の形式の版 -/
def currentVersion : Nat := 1

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
deriving Repr, DecidableEq

def Side.matches : Side → Bool → Bool
  | .self, mine => mine
  | .opp, mine => !mine
  | .both, _ => true

def Selector.matches (s : Selector) (v : View) : Bool :=
  s.types.contains v.type && s.tags.all v.tags.contains && s.side.matches v.mine &&
    (!s.faceUpOnly || v.faceUp) && !(s.excludeSelf && v.isSelf)

/-! ## 形式の検査

中間表現として意味が通るかを調べ、問題をすべて日本語で返す。空なら `WellFormed`。
-/

/-- リストの重複した要素 -/
def dups [BEq α] (l : List α) : List α :=
  (l.filter fun a => l.count a > 1).eraseDups

namespace Selector
def check (r : Rules) (where_ : String) (s : Selector) : List String :=
  (if s.types.isEmpty then [s!"{where_}：範囲のカードの種類が空です"] else []) ++
  (s.types.filter (!r.cardTypes.contains ·)).map
    (s!"{where_}：範囲のカードの種類「{·}」はルールにありません")
end Selector

def Action.check (r : Rules) (where_ : String) : Action → List String
  | .destroy s => s.check r s!"{where_}の破壊"
  | .bounce s => s.check r s!"{where_}の手札に戻す動き"
  | .draw n => if n = 0 then [s!"{where_}：ドローの枚数が0です"] else []

def Effect.check (r : Rules) (where_ : String) : Effect → List String
  | .activated as => (if as.isEmpty then [s!"{where_}：発動する効果に動きがありません"] else []) ++
      as.flatMap (·.check r where_)
  | .negate s => s.check r s!"{where_}の無効"

def Card.check (r : Rules) (c : Card) : List String :=
  (if r.cardTypes.contains c.type then [] else
    [s!"カード「{c.name}」：種類「{c.type}」はルールにありません"]) ++
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
    [s!"{w}：デッキや墓地の役割のゾーンには、すべての種類のカードを置けるようにしてください"] else [])

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
  r.zones.flatMap (·.check r)

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

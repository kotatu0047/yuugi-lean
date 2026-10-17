import CardGen.Play
import CardGen.Report

/-!
# ユーザーが追加する命題と、証明のジョブ

ルールから自動で導く★（`derived`）のほかに、ユーザーは自分で命題を追加できる。
今のところ追加できるのは「フィールド上の、条件に合うカードは最大 `n` 枚」という形
（`CustomClaim`）。カードの種類だけでなくタグでも絞れるので、カードの一覧によっては
自動の★より強いことが言え、その証明は自動ではできない。

流れ：

1. 反例を探す（`CustomClaim.findCounterexample`）。カードの一覧から作ったデッキで、
   条件に合うカードをできるだけフィールドに置く対戦を `State.step?` で実際に進める。
   `step?_sound` があるので、見つかった対戦は本物の反例（到達できる状態）
2. 反例がなければ、証明のジョブを書き出す（`CustomClaim.jobSource`）。
   ジョブは `sorry` で始まる Lean のファイルで、証明する側（開発中は Claude）が埋める
3. `jobs/accept.py` が、文面が変わっていないこと・`sorry` や余計な公理がないことを
   機械的に確かめて受け入れる（`jobs/README.md`）
-/

namespace CardGen
open Lean

/-- ユーザーが追加する命題：フィールド上の、条件に合うカードは最大 `n` 枚 -/
structure CustomClaim where
  /-- 人が読む形の文 -/
  title : String
  /-- カードの種類（このどれか。空なら条件なし） -/
  types : List TypeName
  /-- タグ（このすべてを持つ） -/
  tags : List String
  /-- 両プレイヤーの合計か（`false` なら1人分） -/
  both : Bool
  n : Nat
deriving Repr, DecidableEq, FromJson, ToJson

def CustomClaim.matches (c : CustomClaim) (card : Card) : Bool :=
  (c.types.isEmpty || c.types.contains card.type) && c.tags.all card.tags.contains

/-- フィールド上の、`q` に合うカードの枚数 -/
def countWhere (r : Rules) (q : Card → Bool) (s : PState) : Nat :=
  (s.field.filter fun sl => r.onFieldZone sl.zone && q sl.card).length

def CustomClaim.Holds (c : CustomClaim) (r : Rules) (g : State) : Prop :=
  if c.both then countWhere r c.matches (g true) + countWhere r c.matches (g false) ≤ c.n
  else ∀ p, countWhere r c.matches (g p) ≤ c.n

/-- 証明すべき文：カードの一覧から作ったどのデッキで始めても、到達できるどの状態でも成り立つ -/
def CustomClaim.Statement (c : CustomClaim) (r : Rules) (cards : List Card) : Prop :=
  ∀ decks : PlayerId → List Card, (∀ p, (decks p).length = r.deckSize) → (∀ p, ∀ x ∈ decks p, x ∈ cards) →
    ∀ g, Reachable r decks g → c.Holds r g

/-! ## 反例探し -/

/-- 反例：デッキと、そこから進めた動きの列と、最後の状態での枚数 -/
structure Counterexample where
  decks : List (List String)
  choices : List Choice
  count : Nat
deriving Repr

/-- `p` が、`q` に合う手札を置けるだけ置く（引ける限り引く）動きの列 -/
def greedyPlace (r : Rules) (q : Card → Bool) (p : PlayerId) (fuel : Nat) (g : State) (acc : List Choice) :
    State × List Choice :=
  match fuel with
  | 0 => (g, acc)
  | fuel + 1 =>
    let s := g p
    let place := (List.range s.hand.length).findSome? fun h =>
      if (s.hand[h]?.map q).getD false then
        (List.range r.zones.length).findSome? fun i =>
          let ch := Choice.place p h i true
          (g.step? r ch).map (ch, ·)
      else none
    match place with
    | some (ch, g') => greedyPlace r q p fuel g' (acc ++ [ch])
    | none =>
      match g.step? r (.draw p) with
      | some g' => greedyPlace r q p fuel g' (acc ++ [.draw p])
      | none => (g, acc)

/-- 条件に合うカードだけを繰り返したデッキで、置けるだけ置いてみる。命題を破れば反例 -/
def CustomClaim.findCounterexample (c : CustomClaim) (r : Rules) (cards : List Card) : Option Counterexample :=
  let pool := cards.filter c.matches
  if pool.isEmpty then none else
  let deck := (List.range r.deckSize).map fun i => pool[i % pool.length]!
  let g0 := start r fun _ => deck
  let fuel := 3 * r.deckSize + 3
  let (g1, chs1) := greedyPlace r c.matches true fuel g0 []
  let (g2, chs2) := if c.both then greedyPlace r c.matches false fuel g1 chs1 else (g1, chs1)
  let count := if c.both then countWhere r c.matches (g2 true) + countWhere r c.matches (g2 false)
    else countWhere r c.matches (g2 true)
  if count > c.n then some ⟨[deck.map (·.name), deck.map (·.name)], chs2, count⟩ else none

/-! ## ジョブのファイル -/

/-- 値を Lean のソースにする（次の行から字下げして書くので、複数行の構造体も読める） -/
def leanSource {α} [Repr α] (a : α) : String :=
  "\n" ++ "\n".intercalate (((repr a).pretty 100).splitOn "\n" |>.map ("  " ++ ·))

/-- ジョブの Lean ファイルの、変えてはいけない頭の部分（`JobStatement` までの定義） -/
def CustomClaim.jobHeader (c : CustomClaim) (r : Rules) (cards : List Card) (id : String) : String :=
  s!"import CardGen
open CardGen

/-! 証明のジョブ {id}：{c.title} -/

namespace Job_{id}

def rules : Rules := {leanSource r}

def cards : List Card := {leanSource cards}

def claim : CustomClaim := {leanSource c}

/-- 証明すべき文 -/
def JobStatement : Prop := claim.Statement rules cards

"

/-- 証明を書く部分の最初の形（`job_proof` を `sorry` で置く） -/
def jobProofTemplate : String :=
  "-- ここに証明を書く（補題を足してよい）。最後に `job_proof : JobStatement` を定義すること
theorem job_proof : JobStatement := by
  sorry
"

/-- ジョブの説明（`job.json`） -/
def CustomClaim.jobJson (c : CustomClaim) (g : Game) (id : String) : Json :=
  json% {id: $(id), kind: "customClaim", title: $(c.title), claim: $(toJson c), game: $(toJson g),
         header: $(c.jobHeader g.rules g.cards id)}

end CardGen

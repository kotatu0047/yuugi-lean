import CardGen.Play
import CardGen.Report

/-!
# ユーザーが追加する命題と、証明のジョブ

ルールから自動で導く★（`derived`）のほかに、ユーザーは自分で命題を追加できる。
今のところ追加できるのは「（フィールド上・手札・墓地・デッキ）の、条件に合うカードは最大 `n` 枚」
という形（`CustomClaim`）。カードの種類だけでなくタグでも絞れるので、カードの一覧によっては
自動の★より強いことが言え、その証明は自動ではできない。

流れ：

1. 反例を探す（`CustomClaim.findCounterexample`）。カードの一覧から作ったいくつかのデッキで、
   条件に合うカードをできるだけ命題の場所に集める対戦を `State.step?` で実際に進める。
   `step?_sound` があるので、見つかった対戦は本物の反例（到達できる状態）
2. 反例がなければ、証明のジョブを書き出す（`CustomClaim.jobSource`）。
   ジョブは `sorry` で始まる Lean のファイルで、証明する側（開発中は Claude）が埋める
3. `jobs/accept.py` が、文面が変わっていないこと・`sorry` や余計な公理がないことを
   機械的に確かめて受け入れる（`jobs/README.md`）
-/

namespace CardGen
open Lean

/-- 命題で数える場所 -/
inductive Place
  | field | hand | grave | deck
deriving Repr, DecidableEq, FromJson, ToJson

def Place.label : Place → String
  | .field => "フィールド上" | .hand => "手札" | .grave => "墓地" | .deck => "デッキ"

/-- ユーザーが追加する命題：`place` の、条件に合うカードは最大 `n` 枚 -/
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
  /-- 数える場所（版 1 の命題はフィールド上だけだったので、省くとフィールド上） -/
  place : Place := .field
deriving Repr, DecidableEq, ToJson

instance : FromJson CustomClaim where
  fromJson? j := do
    let place ← match j.getObjVal? "place" with
      | .ok v => fromJson? v
      | .error _ => pure Place.field
    return { title := ← j.getObjValAs? String "title", types := ← j.getObjValAs? (List TypeName) "types",
             tags := ← j.getObjValAs? (List String) "tags", both := ← j.getObjValAs? Bool "both",
             n := ← j.getObjValAs? Nat "n", place }

def CustomClaim.matches (c : CustomClaim) (card : Card) : Bool :=
  (c.types.isEmpty || c.types.contains card.type) && c.tags.all card.tags.contains

/-- フィールド上の、`q` に合うカードの枚数 -/
def countWhere (r : Rules) (q : Card → Bool) (s : PState) : Nat :=
  (s.field.filter fun sl => r.onFieldZone sl.zone && q sl.card).length

/-- 1人分の、命題の場所にある条件に合うカードの枚数 -/
def CustomClaim.count (c : CustomClaim) (r : Rules) (s : PState) : Nat :=
  match c.place with
  | .field => countWhere r c.matches s
  | .hand => (s.hand.filter c.matches).length
  | .grave => (s.grave.filter c.matches).length
  | .deck => (s.deck.filter c.matches).length

def CustomClaim.Holds (c : CustomClaim) (r : Rules) (g : State) : Prop :=
  if c.both then c.count r (g true) + c.count r (g false) ≤ c.n
  else ∀ p, c.count r (g p) ≤ c.n

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

/-- `p` がその時点でできる動き（解決は無効にされていない場合だけ） -/
def choicesFor (r : Rules) (g : State) (p : PlayerId) : List Choice :=
  let s := g p
  let res := (List.range s.field.length).flatMap fun k =>
    (List.range ((s.field[k]?.map (·.card.effects.length)).getD 0)).map fun e => Choice.resolve p k e true
  let pl := (List.range s.hand.length).flatMap fun h =>
    (List.range r.zones.length).flatMap fun i => [Choice.place p h i true, Choice.place p h i false]
  res ++ pl ++ [.draw p]

/-- 命題の数える枚数（`both` なら合計、そうでなければ `true` のプレイヤー） -/
def CustomClaim.total (c : CustomClaim) (r : Rules) (g : State) : Nat :=
  if c.both then c.count r (g true) + c.count r (g false) else c.count r (g true)

/-- 2手先まで見て枚数が一番増える動きを選ぶことを繰り返す。増える動きがなければ引き、引けなければ止まる -/
def lookaheadPlay (c : CustomClaim) (r : Rules) (p : PlayerId) : Nat → State → List Choice → State × List Choice
  | 0, g, acc => (g, acc)
  | fuel + 1, g, acc =>
    let now := c.total r g
    let score (ch : Choice) : Option (Nat × State) := (g.step? r ch).map fun g1 =>
      let best2 := (choicesFor r g1 p).foldl (fun m ch2 =>
        match g1.step? r ch2 with
        | some g2 => max m (c.total r g2)
        | none => m) 0
      (max (c.total r g1) best2, g1)
    let best := (choicesFor r g p).foldl (fun (b : Option (Nat × Choice × State)) ch =>
      match score ch with
      | some (v, g1) => if v > now && (b.all fun b => v > b.1) then some (v, ch, g1) else b
      | none => b) none
    match best with
    | some (_, ch, g1) => lookaheadPlay c r p fuel g1 (acc ++ [ch])
    | none =>
      match g.step? r (.draw p) with
      | some g1 => lookaheadPlay c r p fuel g1 (acc ++ [.draw p])
      | none => (g, acc)

/-- 試すデッキ：条件に合うカードだけを繰り返したもの、合うカードとほかの1種類を交互に並べたもの -/
def CustomClaim.trialDecks (c : CustomClaim) (r : Rules) (cards : List Card) : List (List Card) :=
  let pool := cards.filter c.matches
  let cycle (l : List Card) : List Card :=
    if l.isEmpty then [] else (List.range r.deckSize).map fun i => l[i % l.length]!
  let mixed := (cards.filter (!c.matches ·)).map fun x => cycle (pool.flatMap fun y => [y, x])
  (if pool.isEmpty then [] else [cycle pool]) ++ (if pool.isEmpty then [] else mixed)

/-- 試すデッキのそれぞれで、条件に合うカードを命題の場所に集めるように対戦を進めてみる。
命題を破れば反例（`step?_sound` により本物の到達できる状態） -/
def CustomClaim.findCounterexample (c : CustomClaim) (r : Rules) (cards : List Card) : Option Counterexample :=
  let fuel := 3 * r.deckSize + 3
  (c.trialDecks r cards).findSome? fun deck =>
    let g0 := start r fun _ => deck
    let (g1, chs1) :=
      if c.place == .field then greedyPlace r c.matches true fuel g0 [] else lookaheadPlay c r true fuel g0 []
    let (g2, chs2) := if !c.both then (g1, chs1)
      else if c.place == .field then greedyPlace r c.matches false fuel g1 chs1
      else lookaheadPlay c r false fuel g1 chs1
    let count := c.total r g2
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

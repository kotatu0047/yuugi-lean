import CardGen.Inv

/-!
# ルールから導く性質（★）

ルールを4つの型に当てはめて★を列挙し（`derived`）、列挙した★がすべて成り立つことを
一度だけ証明する（`derived_sound`）。ユーザーがどんなルールを作っても、★の証明はこの定理に
設定値を当てはめるだけで済む。

| 型 | 規則 |
|---|---|
| A. 初期配置 | 開始時のデッキ ＝ デッキの枚数 − 初期手札、開始時の手札 ＝ 初期手札 |
| B. 容量 | ある種類のカードの自分のフィールド上の最大数 ＝ その種類を置ける「フィールド上」のゾーンのマスの数の合計 |
| C. 対称 | フィールド全体の最大数 ＝ 自分の最大数 × 2（共通ルール②） |
| D. 保存 | カードの総数 ＝ デッキの枚数 × 2（共通ルール①） |
| E. 戻らない | デッキの最大数 ＝ デッキの枚数 − 初期手札（デッキにカードを戻す動きがない） |

B と C は、その種類を置ける「フィールド上」のゾーンがすべて「1枚まで」のときだけ列挙する
（「何枚でも」のゾーンがあれば上限はない）。
-/

namespace CardGen

/-- ★の中身 -/
inductive ClaimProp
  /-- ゲーム開始時、どちらのデッキも `n` 枚 -/
  | deckAtStart (n : Nat)
  /-- ゲーム開始時、どちらの手札も `n` 枚 -/
  | handAtStart (n : Nat)
  /-- カードの総数は常に `n` 枚 -/
  | totalCards (n : Nat)
  /-- フィールド上の種類 `t` のカード（`none` なら全種類）は常に最大 `n` 枚。
      `both` なら両プレイヤーの合計、そうでなければ1人分 -/
  | fieldMax (t : Option TypeName) (both : Bool) (n : Nat)
  /-- どちらのデッキも常に最大 `n` 枚 -/
  | deckMax (n : Nat)
  /-- どちらのライフも常に最大 `n`（カードの一覧によって決まる★。`Pool.lean`） -/
  | lifeMax (n : Nat)
  /-- どちらのライフも常に `n` 以上（カードの一覧によって決まる★。`Pool.lean`） -/
  | lifeMin (n : Nat)
  /-- フィールドのどのカードの攻撃力も常に `a + 2 * (b * f)` 以下（カードの一覧によって決まる★。`PoolClaims.lean`）。
      `a`：カードに書いた攻撃力の最大、`b`：1枚の永続の攻撃力の変化の合計の最大、`f`：1人分のフィールド上のカードの最大数 -/
  | atkMax (a b f : Nat)
  /-- フィールドのどのカードの守備力も常に `a + 2 * (b * f)` 以下（`atkMax` の守備力版） -/
  | defMax (a b f : Nat)
deriving Repr, DecidableEq

/-- フィールド上の、種類 `t` のカードの枚数 -/
def fieldCount (r : Rules) (t : Option TypeName) (s : PState) : Nat :=
  (s.field.filter fun sl => r.onFieldZone sl.zone && t.all (· == sl.card.type)).length

def ClaimProp.atStart : ClaimProp → Bool
  | .deckAtStart _ | .handAtStart _ => true
  | _ => false

/-- 状態 `g` で成り立つ -/
def ClaimProp.Holds (r : Rules) (g : State) : ClaimProp → Prop
  | .deckAtStart n => ∀ p, (g p).deck.length = n
  | .handAtStart n => ∀ p, (g p).hand.length = n
  | .totalCards n => (g true).size + (g false).size = n
  | .fieldMax t false n => ∀ p, fieldCount r t (g p) ≤ n
  | .fieldMax t true n => fieldCount r t (g true) + fieldCount r t (g false) ≤ n
  | .deckMax n => ∀ p, (g p).deck.length ≤ n
  | .lifeMax n => ∀ p, (g p).life ≤ n
  | .lifeMin n => ∀ p, n ≤ (g p).life
  | .atkMax a b f => ∀ p k sl neg, (g p).field[k]? = some sl → g.atkOf r neg (p, k) sl ≤ a + 2 * (b * f)
  | .defMax a b f => ∀ p k sl neg, (g p).field[k]? = some sl → g.defOf r neg (p, k) sl ≤ a + 2 * (b * f)

/-- ★として正しい：開始時の性質は開始時に、それ以外は到達できるどの状態でも成り立つ -/
def ClaimProp.Valid (r : Rules) (decks : PlayerId → List Card) (c : ClaimProp) : Prop :=
  if c.atStart then c.Holds r (start r decks) else ∀ g, Reachable r decks g → c.Holds r g

/-! ## 型 B の上限 -/

/-- ゾーン `z` が、種類 `t` のカードを置ける「フィールド上」のゾーンか -/
def Zone.holds (z : Zone) (t : Option TypeName) : Bool :=
  z.role == .plain && z.onField && t.all z.admits.contains

/-- 種類 `t` を置ける「フィールド上」のゾーンがすべて「1枚まで」 -/
def Rules.bounded (r : Rules) (t : Option TypeName) : Bool :=
  r.zones.all fun z => !z.holds t || z.capacity == .one

/-- 種類 `t` の、1人分のフィールド上の上限 -/
def Rules.bound (r : Rules) (t : Option TypeName) : Nat :=
  ((List.range r.zones.length).map fun i =>
    match r.zones[i]? with
    | some z => if z.holds t then z.count else 0
    | none => 0).sum

theorem sum_map_add (l : List Nat) (f g : Nat → Nat) :
    (l.map fun i => f i + g i).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => rfl
  | cons a t ih => simp only [List.map_cons, List.sum_cons, ih]; omega

theorem sum_map_zero (l : List Nat) : (l.map fun _ => 0).sum = 0 := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [ih]

theorem sum_map_le (l : List Nat) (f g : Nat → Nat) (h : ∀ i ∈ l, f i ≤ g i) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => exact Nat.le_refl _
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add (h a (List.mem_cons_self ..)) (ih fun i hi => h i (List.mem_cons_of_mem _ hi))

theorem sum_indicator (j n : Nat) :
    ((List.range n).map fun i => if j == i then 1 else 0).sum = if j < n then 1 else 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih]
    by_cases h1 : j < n
    · have : j ≠ n := by omega
      simp [h1, this, show j < n + 1 by omega]
    · by_cases h2 : j = n
      · subst h2; simp
      · simp [h1, h2, show ¬ j < n + 1 by omega]

/-- ゾーンの番号が `n` 未満のカードの枚数は、ゾーンごとの枚数の合計 -/
theorem length_eq_sum_zones (n : Nat) (l : List Slot) (h : ∀ sl ∈ l, sl.zone < n) :
    l.length = ((List.range n).map fun i => (l.filter (·.zone == i)).length).sum := by
  induction l with
  | nil => simp [sum_map_zero]
  | cons a t ih =>
    have ht := ih fun sl hm => h sl (List.mem_cons_of_mem _ hm)
    have hlen : ∀ i, ((a :: t).filter (·.zone == i)).length =
        (if a.zone == i then 1 else 0) + (t.filter (·.zone == i)).length := by
      intro i; by_cases hi : a.zone = i <;> simp [hi] <;> omega
    simp only [hlen]
    rw [sum_map_add, sum_indicator, ← ht, ite_eq_left (h a (List.mem_cons_self ..))]
    simp; omega

theorem length_filter_filter_le {α} (p q : α → Bool) (l : List α) :
    ((l.filter p).filter q).length ≤ (l.filter q).length :=
  (List.filter_sublist.filter q).length_le


/-- 盤面の制約が成り立っていれば、1人分のフィールド上の種類 `t` のカードは上限以下 -/
theorem fieldCount_le_bound {r : Rules} {g : State} (h : Inv r g) (p : PlayerId) {t : Option TypeName}
    (hb : r.bounded t = true) : fieldCount r t (g p) ≤ r.bound t := by
  let P := fun sl : Slot => r.onFieldZone sl.zone && t.all (· == sl.card.type)
  have hlt : ∀ sl ∈ (g p).field.filter P, sl.zone < r.zones.length := by
    intro sl hm
    obtain ⟨z, hz, -⟩ := h.zones p sl (List.mem_filter.1 hm).1
    exact (List.getElem?_eq_some_iff.1 hz).1
  unfold fieldCount Rules.bound
  rw [length_eq_sum_zones _ _ hlt]
  apply sum_map_le
  intro i hi
  have hi' : i < r.zones.length := List.mem_range.1 hi
  obtain ⟨z, hz⟩ : ∃ z, r.zones[i]? = some z := ⟨_, List.getElem?_eq_getElem hi'⟩
  simp only [hz]
  by_cases hh : z.holds t = true
  · simp only [hh, ite_true]
    have hcap : z.capacity = .one := by
      have := List.all_eq_true.1 hb z (List.mem_of_getElem? hz)
      simp [hh] at this; exact this
    exact Nat.le_trans (length_filter_filter_le _ _ _) (h.cap p i z hz hcap)
  · simp only [hh]
    suffices ((g p).field.filter P).filter (·.zone == i) = [] by simp [this]
    refine List.filter_eq_nil_iff.2 fun sl hm hzi => hh ?_
    have hzi : sl.zone = i := by simpa using hzi
    have hm' := List.mem_filter.1 hm
    obtain ⟨z', hz', -, hadm, -⟩ := h.zones p sl hm'.1
    rw [hzi, hz] at hz'
    cases hz'
    have hP := hm'.2
    simp only [P, Rules.onFieldZone, hzi, hz, Bool.and_eq_true] at hP
    simp only [Zone.holds, Bool.and_eq_true]
    refine ⟨hP.1, ?_⟩
    cases t with
    | none => rfl
    | some t => simp at hP ⊢; rw [hP.2]; simpa using hadm

/-! ## ★の列挙 -/

/-- 型 A〜D に当てはめた★の中身 -/
def derivedProps (r : Rules) : List ClaimProp :=
  [.deckAtStart (r.deckSize - r.handSize)] ++
  (if r.handSize ≤ r.deckSize then [.handAtStart r.handSize] else []) ++
  [.totalCards (2 * r.deckSize), .deckMax (r.deckSize - r.handSize)] ++
  ((none :: r.cardTypes.map some).filter r.bounded).flatMap fun t =>
    [.fieldMax t false (r.bound t), .fieldMax t true (2 * r.bound t)]

/-- **列挙した★は、どれもすべての対戦で成り立つ**（デッキの枚数がルールどおりなら） -/
theorem derived_sound (r : Rules) (decks : PlayerId → List Card)
    (hd : ∀ p, (decks p).length = r.deckSize) : ∀ c ∈ derivedProps r, c.Valid r decks := by
  intro c hc
  simp only [derivedProps, List.mem_append, List.mem_flatMap, List.mem_filter,
    List.mem_cons, List.mem_map, List.not_mem_nil, or_false] at hc
  rcases hc with ((rfl | hc) | rfl | rfl) | ⟨t, ⟨-, hb⟩, rfl | rfl⟩
  · intro p; simp [start, hd p]
  · by_cases hh : r.handSize ≤ r.deckSize
    · simp only [hh, ite_true, List.mem_singleton] at hc; subst hc
      intro p; simp [start, hd p]; omega
    · simp [hh] at hc
  · simp only [ClaimProp.Valid, ClaimProp.atStart]
    intro g hg
    have h := hg.inv hd
    show (g true).size + (g false).size = 2 * r.deckSize
    rw [h.size, h.size]; omega
  · simp only [ClaimProp.Valid, ClaimProp.atStart]
    intro g hg p
    exact (hg.inv hd).deck p
  · simp only [ClaimProp.Valid, ClaimProp.atStart]
    intro g hg p
    exact fieldCount_le_bound (hg.inv hd) p hb
  · simp only [ClaimProp.Valid, ClaimProp.atStart]
    intro g hg
    have h := hg.inv hd
    show fieldCount r t (g true) + fieldCount r t (g false) ≤ 2 * r.bound t
    have := fieldCount_le_bound h true hb
    have := fieldCount_le_bound h false hb
    omega

end CardGen

namespace CardGen

/-! ## 人が読む形の★ -/

/-- ★：中身と、その文章と根拠 -/
structure Claim where
  prop : ClaimProp
  text : String
  grounds : List String
deriving Repr

def Capacity.label : Capacity → String
  | .one => "1枚まで"
  | .many => "何枚でも"

def Zone.label (z : Zone) : String :=
  s!"ゾーン「{z.name}」（{z.count}マス、{z.capacity.label}、置ける種類：{"・".intercalate z.admits}）"

def typeLabel : Option TypeName → String
  | none => "カード"
  | some t => s!"{t}のカード"

def ClaimProp.describe (r : Rules) : ClaimProp → Claim
  | p@(.deckAtStart n) => ⟨p, s!"ゲーム開始時のデッキは各プレイヤー{n}枚",
      [s!"デッキの枚数（{r.deckSize}枚）", s!"初期手札（{r.handSize}枚）"]⟩
  | p@(.handAtStart n) => ⟨p, s!"ゲーム開始時の手札は各プレイヤー{n}枚",
      [s!"初期手札（{r.handSize}枚）", s!"デッキの枚数（{r.deckSize}枚）"]⟩
  | p@(.totalCards n) => ⟨p, s!"カードの総数は常に{n}枚",
      [s!"デッキの枚数（{r.deckSize}枚）", "共通ルール①（プレイヤーは自分と相手の2人）"]⟩
  | p@(.fieldMax t both n) =>
    let zs := (r.zones.filter (·.holds t)).map Zone.label
    let zs := if zs.isEmpty then ["置けるフィールド上のゾーンがない"] else zs
    if both then ⟨p, s!"フィールド全体の{typeLabel t}は最大{n}枚",
      zs ++ ["共通ルール②（相手のフィールドは自分のフィールドを逆さまにした形）"]⟩
    else ⟨p, s!"自分のフィールド上の{typeLabel t}は最大{n}枚", zs⟩
  | p@(.deckMax n) => ⟨p, s!"デッキは各プレイヤー最大{n}枚（増えない）",
      [s!"デッキの枚数（{r.deckSize}枚）", s!"初期手札（{r.handSize}枚）", "デッキにカードを戻す効果の部品がない"]⟩
  | p@(.lifeMax n) => ⟨p, s!"ライフは各プレイヤー最大{n}（初期ライフを超えない）",
      [s!"初期ライフ（{r.life}）", "カードの一覧に「回復」の動きを持つカードがない"]⟩
  | p@(.lifeMin n) => ⟨p, s!"ライフは各プレイヤー最小{n}（初期ライフより減らない）",
      [s!"初期ライフ（{r.life}）", "カードの一覧に「ダメージ」の動きを持つカードがない",
       "ルールに戦闘できる種類がない（攻撃でライフが減ることはない）"]⟩
  | p@(.atkMax a b f) => ⟨p, s!"フィールドのカードの攻撃力は最大{a + 2 * (b * f)}",
      [s!"カードに書いた攻撃力の最大（{a}）",
       if b = 0 then "カードの一覧に、攻撃力を上げる永続の効果を持つカードがない" else
         s!"1枚の永続の攻撃力の変化の合計の最大（+{b}）× フィールド上のカードの最大数（両プレイヤーで{2 * f}枚）",
       "カードの一覧に、攻撃力を上げる「ターンの終わりまでの変化」を持つカードがない"]⟩
  | p@(.defMax a b f) => ⟨p, s!"フィールドのカードの守備力は最大{a + 2 * (b * f)}",
      [s!"カードに書いた守備力の最大（{a}）",
       if b = 0 then "カードの一覧に、守備力を上げる永続の効果を持つカードがない" else
         s!"1枚の永続の守備力の変化の合計の最大（+{b}）× フィールド上のカードの最大数（両プレイヤーで{2 * f}枚）",
       "カードの一覧に、守備力を上げる「ターンの終わりまでの変化」を持つカードがない"]⟩

/-- ルールから導いた★（どれも `derived_sound` で証明済み） -/
def derived (r : Rules) : List Claim := (derivedProps r).map (·.describe r)

@[simp] theorem ClaimProp.describe_prop (r : Rules) (p : ClaimProp) : (p.describe r).prop = p := by
  cases p with
  | fieldMax t both n => cases both <;> rfl
  | _ => rfl

/-- **人が読む形の★も、どれもすべての対戦で成り立つ** -/
theorem derived_valid (r : Rules) (decks : PlayerId → List Card)
    (hd : ∀ p, (decks p).length = r.deckSize) : ∀ c ∈ derived r, c.prop.Valid r decks := by
  intro c hc
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hc
  rw [ClaimProp.describe_prop]
  exact derived_sound r decks hd p hp

end CardGen

import CardGen.Claims

/-!
# 無効の関係の判定

フィールドの `n` 枚のカード（番号 `0 … n-1`）と、「`y` が `x` の効果を無効にする」関係 `rel y x` を考える。
各カードは有効か無効かのどちらかで、次の状態を「安定」と呼ぶ。

- 有効なカードは、どの有効なカードにも無効にされていない
- 無効なカードは、ある有効なカードに無効にされている

判定の手続きは、安定の条件に合わないカードを1枚選んで有効・無効を反転することを、
合わないカードがなくなるまで繰り返す（どのカードを選ぶかは自由）。

**メタ定理1**（`System.settles`）：関係に順位付け（`y` が `x` を無効にするなら `y` の順位は
`x` より小さい）があれば、

- どの状態から、どの順番で選んでも、手続きは必ず止まる
- 安定な状態はちょうど1つ（止まったときの結果は、選び方によらず1通り）

順位付けがあることは、関係に循環がないことと同じ。
-/

namespace CardGen

/-- フィールドのカードと無効の関係 -/
structure System where
  n : Nat
  /-- `rel y x`：`y` が `x` の効果を無効にする -/
  rel : Nat → Nat → Bool

namespace System

variable (S : System)

/-- `x` が、有効なカード（`f`）のどれかに無効にされている -/
def negated (f : Nat → Bool) (x : Nat) : Bool :=
  (List.range S.n).any fun y => S.rel y x && f y

/-- `x` が安定の条件に合わない（有効なのに無効にされている、または無効なのに誰にも無効にされていない） -/
def wrong (f : Nat → Bool) (x : Nat) : Bool := f x == S.negated f x

def Stable (f : Nat → Bool) : Prop := ∀ x < S.n, S.wrong f x = false

/-- `x` の有効・無効を反転する -/
def flip (f : Nat → Bool) (x : Nat) : Nat → Bool := fun y => if y = x then !f x else f y

/-- 判定の手続きの1歩 -/
inductive Step : (Nat → Bool) → (Nat → Bool) → Prop
  | mk (f : Nat → Bool) (x : Nat) : x < S.n → S.wrong f x = true → Step f (flip f x)

/-- 順位付け：`y` が `x` を無効にするなら `y` の順位は `x` より小さい -/
def Ranked (rank : Nat → Nat) : Prop :=
  ∀ y < S.n, ∀ x < S.n, S.rel y x = true → rank y < rank x

variable {S}

theorem stable_iff_eq (f : Nat → Bool) (x : Nat) : S.wrong f x = false ↔ f x = !S.negated f x := by
  unfold wrong; cases f x <;> cases S.negated f x <;> decide

theorem any_congr_mem {α} (l : List α) (p q : α → Bool) (h : ∀ a ∈ l, p a = q a) : l.any p = l.any q := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp only [List.any_cons, h a (List.mem_cons_self ..), ih fun b hb => h b (List.mem_cons_of_mem _ hb)]

/-- `x` が無効にされているかは、`x` より順位の小さいカードの有効・無効だけで決まる -/
theorem negated_congr {rank : Nat → Nat} (hr : S.Ranked rank) {f g : Nat → Bool} {x : Nat} (hx : x < S.n)
    (h : ∀ y < S.n, rank y < rank x → f y = g y) : S.negated f x = S.negated g x := by
  unfold negated
  apply any_congr_mem
  intro y hy
  have hy' := List.mem_range.1 hy
  cases hrel : S.rel y x
  · rfl
  · simp [h y hy' (hr y hy' x hx hrel)]

/-- **安定な状態は高々1つ** -/
theorem stable_unique {rank : Nat → Nat} (hr : S.Ranked rank) {f g : Nat → Bool} (hf : S.Stable f)
    (hg : S.Stable g) : ∀ x < S.n, f x = g x := by
  suffices ∀ k, ∀ x < S.n, rank x < k → f x = g x from fun x hx => this _ x hx (Nat.lt_succ_self _)
  intro k
  induction k with
  | zero => intro x _ h; exact absurd h (Nat.not_lt_zero _)
  | succ k ih =>
    intro x hx hk
    rw [(stable_iff_eq f x).1 (hf x hx), (stable_iff_eq g x).1 (hg x hx),
      negated_congr hr hx fun y hy hyx => ih y hy (by omega)]

/-! ## 手続きが止まること -/

/-- 順位 `k` の、条件に合わないカードの枚数 -/
def count (rank : Nat → Nat) (f : Nat → Bool) (k : Nat) : Nat :=
  ((List.range S.n).filter fun x => rank x == k && S.wrong f x).length

/-- 底 `B` の数字の並びが表す数（先頭が一番上の位） -/
def digits (B : Nat) (l : List Nat) : Nat := l.foldl (fun acc d => acc * B + d) 0

theorem digits_append_single (B : Nat) (l : List Nat) (d : Nat) :
    digits B (l ++ [d]) = digits B l * B + d := by
  simp [digits, List.foldl_append]

theorem map_range_congr (F G : Nat → Nat) (L : Nat) (h : ∀ j < L, F j = G j) :
    (List.range L).map F = (List.range L).map G :=
  List.map_congr_left fun j hj => h j (List.mem_range.1 hj)

/-- 上の位がすべて同じで、`k` の位が小さく、下の位がどれも `B` 未満なら、表す数は小さい -/
theorem digits_lt (B : Nat) (F G : Nat → Nat) (k : Nat) (hFG : ∀ j < k, F j = G j) (hk : G k < F k)
    (hB : ∀ j, G j < B) : ∀ L, k < L → digits B ((List.range L).map G) < digits B ((List.range L).map F) := by
  intro L hL
  induction L with
  | zero => exact absurd hL (Nat.not_lt_zero _)
  | succ L ih =>
    rw [List.range_succ, List.map_append, List.map_append, List.map_singleton, List.map_singleton,
      digits_append_single, digits_append_single]
    by_cases hkL : k < L
    · have h1 := ih hkL
      have h2 := hB L
      calc digits B ((List.range L).map G) * B + G L
          < (digits B ((List.range L).map G) + 1) * B := by rw [Nat.add_mul]; omega
        _ ≤ digits B ((List.range L).map F) * B := Nat.mul_le_mul_right _ h1
        _ ≤ _ := Nat.le_add_right _ _
    · have hkL' : k = L := by omega
      subst hkL'
      rw [map_range_congr F G k hFG]
      omega

theorem length_filter_le_of_imp {α} (l : List α) (p q : α → Bool) (h : ∀ a ∈ l, q a = true → p a = true) :
    (l.filter q).length ≤ (l.filter p).length := by
  induction l with
  | nil => exact Nat.le_refl _
  | cons a t ih =>
    have iht := ih fun b hb => h b (List.mem_cons_of_mem _ hb)
    cases hq : q a <;> cases hp : p a <;> simp [hq, hp]
    · omega
    · omega
    · exact absurd (h a (List.mem_cons_self ..) hq) (by simp [hp])
    · omega

theorem length_filter_lt_of_imp {α} (l : List α) (p q : α → Bool) (h : ∀ a ∈ l, q a = true → p a = true)
    (x : α) (hx : x ∈ l) (hpx : p x = true) (hqx : q x = false) : (l.filter q).length < (l.filter p).length := by
  induction l with
  | nil => exact absurd hx (List.not_mem_nil)
  | cons a t ih =>
    have h' : ∀ b ∈ t, q b = true → p b = true := fun b hb => h b (List.mem_cons_of_mem _ hb)
    rcases List.mem_cons.1 hx with rfl | hxt
    · have := length_filter_le_of_imp t p q h'
      simp [hpx, hqx]; omega
    · have := ih h' hxt
      cases hq : q a <;> cases hp : p a <;> simp [hq, hp]
      · omega
      · omega
      · exact absurd (h a (List.mem_cons_self ..) hq) (by simp [hp])
      · omega

/-- 反転したカードより順位が小さくないカード以外は、条件に合うかどうかが変わらない -/
theorem wrong_flip_of_ne {rank : Nat → Nat} (hr : S.Ranked rank) {f : Nat → Bool} {x i : Nat}
    (hi : i < S.n) (hix : i ≠ x) (hrk : ¬ rank x < rank i) : S.wrong (flip f x) i = S.wrong f i := by
  unfold wrong
  have h1 : flip f x i = f i := by simp [flip, hix]
  have h2 : S.negated (flip f x) i = S.negated f i :=
    negated_congr hr hi fun y _ hyi => by
      have : y ≠ x := fun hyx => by subst hyx; exact hrk hyi
      simp [flip, this]
  rw [h1, h2]

/-- **1歩進むと、条件に合わないカードの枚数を順位ごとに並べた数が小さくなる** -/
theorem step_digits_lt {rank : Nat → Nat} (hr : S.Ranked rank) {L : Nat} (hL : ∀ x < S.n, rank x < L)
    {f g : Nat → Bool} (h : S.Step f g) :
    digits (S.n + 1) ((List.range L).map (S.count rank g)) < digits (S.n + 1) ((List.range L).map (S.count rank f)) := by
  cases h with
  | mk x hx hw =>
  have hneg : S.negated (flip f x) x = S.negated f x :=
    negated_congr hr hx fun y _ hyx => by
      have : y ≠ x := fun e => by subst e; exact Nat.lt_irrefl _ hyx
      simp [flip, this]
  have hwx : S.wrong (flip f x) x = false := by
    unfold wrong at hw ⊢
    rw [hneg]; simp only [flip, ite_true]
    cases hfx : f x <;> simp_all
  apply digits_lt _ _ _ (rank x) _ _ _ L (hL x hx)
  · intro j hj
    unfold count; congr 1
    apply List.filter_congr
    intro i hi
    have hi' := List.mem_range.1 hi
    by_cases hij : rank i = j
    · have hix : i ≠ x := fun e => by subst e; omega
      rw [wrong_flip_of_ne hr hi' hix (by omega)]
    · have : (rank i == j) = false := by simpa using hij
      simp [this]
  · unfold count
    refine length_filter_lt_of_imp _ _ _ ?_ x (List.mem_range.2 hx) (by simp [hw]) (by simp [hwx])
    intro i hi hq
    have hi' := List.mem_range.1 hi
    simp only [Bool.and_eq_true, beq_iff_eq] at hq ⊢
    refine ⟨hq.1, ?_⟩
    by_cases hix : i = x
    · subst hix; rw [hwx] at hq; exact absurd hq.2 (by simp)
    · rw [← wrong_flip_of_ne hr hi' hix (by omega)]; exact hq.2
  · intro j
    exact Nat.lt_succ_of_le (Nat.le_trans (List.length_filter_le _ _) (by simp))

/-- **メタ定理1（止まること）**：どの状態から、どの順番で選んでも、手続きは必ず止まる -/
theorem terminates {rank : Nat → Nat} (hr : S.Ranked rank) :
    WellFounded fun g f => S.Step f g := by
  let L := ((List.range S.n).map rank).foldl max 0 + 1
  have hL : ∀ x < S.n, rank x < L := by
    intro x hx
    have : rank x ≤ ((List.range S.n).map rank).foldl max 0 := by
      have hm : rank x ∈ (List.range S.n).map rank := List.mem_map.2 ⟨x, List.mem_range.2 hx, rfl⟩
      suffices ∀ (l : List Nat) (a b : Nat), b ∈ l ∨ b ≤ a → b ≤ l.foldl max a from this _ 0 _ (.inl hm)
      intro l
      induction l with
      | nil => intro a b h; simpa using h
      | cons c t ih =>
        intro a b h
        apply ih
        rcases h with h | h
        · rcases List.mem_cons.1 h with rfl | h
          · exact .inr (Nat.le_max_right _ _)
          · exact .inl h
        · exact .inr (Nat.le_trans h (Nat.le_max_left _ _))
    omega
  exact Subrelation.wf (fun h => step_digits_lt hr hL h)
    (InvImage.wf (fun f => digits (S.n + 1) ((List.range L).map (S.count rank f))) Nat.lt_wfRel.wf)

/-- 止まった状態（もう反転できるカードがない）は安定 -/
theorem stable_of_halt {f : Nat → Bool} (h : ∀ g, ¬ S.Step f g) : S.Stable f := by
  intro x hx
  cases hw : S.wrong f x
  · rfl
  · exact absurd (Step.mk f x hx hw) (h _)

/-- 安定な状態が存在する -/
theorem exists_stable {rank : Nat → Nat} (hr : S.Ranked rank) : ∃ f, S.Stable f := by
  refine (terminates hr).induction (C := fun _ => ∃ f, S.Stable f) (fun _ => false) ?_
  intro f ih
  by_cases h : ∃ g, S.Step f g
  · obtain ⟨g, hg⟩ := h; exact ih g hg
  · exact ⟨f, stable_of_halt fun g hg => h ⟨g, hg⟩⟩

/-- **メタ定理1**：順位付けがあれば、手続きは必ず止まり、安定な状態はちょうど1つ -/
theorem settles {rank : Nat → Nat} (hr : S.Ranked rank) :
    WellFounded (fun g f => S.Step f g) ∧ (∃ f, S.Stable f) ∧
    ∀ f g, S.Stable f → S.Stable g → ∀ x < S.n, f x = g x :=
  ⟨terminates hr, exists_stable hr, fun _ _ hf hg => stable_unique hr hf hg⟩

end System

/-! ## カードから作る関係 -/

/-- フィールドに置かれたカード1枚（実体） -/
structure Inst where
  card : Card
  controller : PlayerId
  faceUp : Bool
deriving Repr

def Effect.negSel : Effect → Option Selector
  | .negate s => some s
  | _ => none

/-- `a` から見た `b` -/
def Inst.viewFrom (b a : Inst) (isSelf : Bool) : View :=
  { type := b.card.type, tags := b.card.tags, mine := b.controller == a.controller,
    faceUp := b.faceUp, isSelf }

/-- 盤面の `y` 番目のカードが `x` 番目のカードの効果を無効にする（`y` が表側表示で、無効の範囲に合う） -/
def instRel (insts : List Inst) (y x : Nat) : Bool :=
  match insts[y]?, insts[x]? with
  | some a, some b => a.faceUp && a.card.effects.any fun e => match e.negSel with
      | some s => s.matches (b.viewFrom a (y == x))
      | none => false
  | _, _ => false

/-- 盤面から作る無効の関係 -/
def System.ofInsts (insts : List Inst) : System := ⟨insts.length, instRel insts⟩

/-- カード `c` のある実体が、カード `d` のある実体を無効にしうる（陣営・表裏・同じ実体かは見ない） -/
def mayNegate (c d : Card) : Bool := c.effects.any fun e => match e.negSel with
  | some s => s.types.contains d.type && s.tags.all d.tags.contains
  | none => false

theorem mayNegate_of_instRel {insts : List Inst} {y x : Nat} (h : instRel insts y x = true) :
    ∃ a b, insts[y]? = some a ∧ insts[x]? = some b ∧ mayNegate a.card b.card = true := by
  unfold instRel at h
  split at h
  · rename_i a b ha hb
    refine ⟨a, b, ha, hb, ?_⟩
    simp only [Bool.and_eq_true, List.any_eq_true] at h
    obtain ⟨e, he, hm⟩ := h.2
    refine List.any_eq_true.2 ⟨e, he, ?_⟩
    cases hs : e.negSel with
    | none => simp [hs] at hm
    | some s =>
      simp only [hs, Selector.matches, Inst.viewFrom, Bool.and_eq_true] at hm
      simp only [hm.1.1.1.1, hm.1.1.1.2, Bool.and_self]
  · simp at h

/-- カードの順位付けの確認：`c` が `d` を無効にしうるなら `c` の順位は `d` より小さい -/
def rankOK (cards : List Card) (rank : Card → Nat) : Bool :=
  cards.all fun c => cards.all fun d => !mayNegate c d || decide (rank c < rank d)

/-- 盤面のカードの順位（カードの順位をそのまま使う） -/
def instRank (insts : List Inst) (rank : Card → Nat) (i : Nat) : Nat :=
  match insts[i]? with
  | some a => rank a.card
  | none => 0

theorem ranked_ofInsts {cards : List Card} {rank : Card → Nat} (hok : rankOK cards rank = true)
    {insts : List Inst} (hin : ∀ a ∈ insts, a.card ∈ cards) :
    (System.ofInsts insts).Ranked (instRank insts rank) := by
  intro y _ x _ h
  obtain ⟨a, b, ha, hb, hm⟩ := mayNegate_of_instRel h
  have hc := List.all_eq_true.1 (List.all_eq_true.1 hok a.card (hin a (List.mem_of_getElem? ha)))
    b.card (hin b (List.mem_of_getElem? hb))
  simp only [hm, Bool.not_true, Bool.false_or, decide_eq_true_eq] at hc
  simp only [instRank, ha, hb]
  exact hc

/-- **メタ定理1（カード版）**：カードの順位付けの確認が通れば、そのカードだけが並ぶ**どの盤面でも**、
無効の判定はどの順番で進めても必ず止まり、結果はただ1通り -/
theorem negation_settles {cards : List Card} {rank : Card → Nat} (hok : rankOK cards rank = true)
    (insts : List Inst) (hin : ∀ a ∈ insts, a.card ∈ cards) :
    let S := System.ofInsts insts
    WellFounded (fun g f => S.Step f g) ∧ (∃ f, S.Stable f) ∧
    ∀ f g, S.Stable f → S.Stable g → ∀ x < S.n, f x = g x :=
  System.settles (ranked_ofInsts hok hin)

/-! ## 検査ツールが使う計算 -/

/-- カードの順位：自分を無効にしうるカードからの最長の道の長さ（循環がなければ `rankOK` が通る） -/
def computeRanks (cards : List Card) : List Nat :=
  let step (rs : List Nat) : List Nat := cards.map fun d =>
    (cards.zip rs).foldl (fun m (c, rc) => if mayNegate c d then max m (rc + 1) else m) 0
  Nat.repeat step cards.length (cards.map fun _ => 0)

def rankFn (cards : List Card) (rs : List Nat) (c : Card) : Nat :=
  match cards.idxOf? c with
  | some i => rs.getD i 0
  | none => 0

/-- 無効にしうる関係の矢印（カード名の組） -/
def negEdges (cards : List Card) : List (String × String) :=
  cards.flatMap fun c => (cards.filter (mayNegate c)).map fun d => (c.name, d.name)

/-- `i` 番目のカードから1歩以上たどって行けるカードの番号 -/
def reachFrom (cards : List Card) (i : Nat) : List Nat :=
  let n := cards.length
  let succ (j : Nat) : List Nat := match cards[j]? with
    | some c => (List.range n).filter fun k => match cards[k]? with
        | some d => mayNegate c d
        | none => false
    | none => []
  let grow (seen : List Nat) : List Nat :=
    seen ++ ((seen.flatMap succ).filter (!seen.contains ·)).eraseDups
  Nat.repeat grow n (succ i)

/-- 循環に含まれるカードを、互いに行き来できるまとまりごとに -/
def negCycles (cards : List Card) : List (List String) :=
  let n := cards.length
  let reach := (List.range n).map (reachFrom cards)
  let onCycle := (List.range n).filter fun i => (reach.getD i []).contains i
  let groups := onCycle.map fun i => onCycle.filter fun j => (reach.getD i []).contains j && (reach.getD j []).contains i
  groups.eraseDups.map fun g => g.filterMap fun j => cards[j]?.map (·.name)

/-- 無効の関係の検査の結果 -/
inductive NegResult
  /-- 無効の効果を持つカードがない -/
  | none
  /-- 循環がなく、メタ定理1で止まることと結果が1通りであることが保証される -/
  | proved
  /-- 循環がある（このまとまりの中で順番によって結果が変わったり、止まらなかったりしうる） -/
  | cyclic (groups : List (List String))
deriving Repr

def checkNegation (cards : List Card) : NegResult :=
  if cards.all (fun c => c.effects.all fun e => e.negSel.isNone) then .none
  else if rankOK cards (rankFn cards (computeRanks cards)) then .proved
  else .cyclic (negCycles cards)

/-- `proved` のときは、メタ定理1が当てはまる -/
theorem checkNegation_proved {cards : List Card} (h : checkNegation cards = .proved) :
    rankOK cards (rankFn cards (computeRanks cards)) = true := by
  unfold checkNegation at h
  split at h
  · cases h
  · split at h
    · assumption
    · cases h

end CardGen

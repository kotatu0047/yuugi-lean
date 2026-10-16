import YuugiLean.Invariants

/-!
# 永続効果の有効・無効の判定は必ず決まる

`settle` は `settleOnce` を繰り返して、有効・無効が変わらなくなるまで進める。カードの組み合わせによっては
回り続けることがある（例：スキルドレイン・王宮のお触れ・「モンスターの効果を無効にするモンスター」・
「罠とモンスターの効果を無効にするモンスター」）。ここでは、次の条件（`AuraSrc.Simple`）を満たすカードだけなら
必ず決まることを証明する。今あるカードはすべてこの条件を満たす。

* モンスターの効果を無効にする効果を持つのは罠カードだけで、その罠は罠の効果を無効にする効果を持たない
* 罠の効果を無効にする効果を持つのは罠カードかモンスターだけ

証明の方針：カードを次の4種類に分ける。
* A：罠を無効にする罠（王宮のお触れ）
* B：モンスターを無効にする罠（スキルドレイン）
* D：罠を無効にするモンスター（サイコ・ショッカー）
* P：何も無効にしないカード

`settleOnce` で1回変えるたびに、次の量が辞書式に減る（`settleMeasure_lt`）。
1. 適用中の種類：D があれば 0、なければ A があれば 1、なければ B があれば 2、なければ 3
2. 適用されていない D・B の枚数
3. 「その種類の、適用中のどのカードよりも適用の時刻が古い」カードの枚数（B は D より、A は A より、D は B より）
4. 適用されていない P の枚数
5. 有効なカードの枚数
-/

namespace YGO

/-- 罠カードの効果を無効にする効果を持つ -/
def AuraSrc.nt (s : AuraSrc) : Bool := s.auras.contains .negateTraps
/-- モンスターの効果を無効にする効果を持つ -/
def AuraSrc.nm (s : AuraSrc) : Bool := s.auras.contains .negateMonsterEffects

theorem AuraSrc.negates_eq (t s : AuraSrc) :
    t.negates s = (decide (t.key ≠ s.key) &&
      ((t.nm && decide (s.kind = .monster)) || (t.nt && decide (s.kind = .trap)))) := by
  unfold AuraSrc.negates AuraSrc.nm AuraSrc.nt
  by_cases hk : t.key = s.key
  · simp [hk]
  simp only [hk, ne_eq, not_false_eq_true, decide_true, Bool.true_and]
  generalize t.auras = as
  cases s.kind <;> simp <;> induction as <;> simp_all <;> rename_i a _ _ <;> cases a <;> simp_all

/-- 永続効果の種類 -/
inductive Cat where
  | A  -- 罠を無効にする罠
  | B  -- モンスターを無効にする罠
  | D  -- 罠を無効にするモンスター
  | P  -- 何も無効にしない
  deriving DecidableEq, Repr

def AuraSrc.cat (s : AuraSrc) : Cat :=
  if s.nt then (if s.kind = .trap then .A else .D) else if s.nm then .B else .P

/-- 判定が必ず決まるカードの条件 -/
def AuraSrc.Simple (s : AuraSrc) : Prop :=
  (s.nm = true → s.kind = .trap ∧ s.nt = false) ∧ (s.nt = true → s.kind ≠ .spell)

instance : DecidablePred AuraSrc.Simple := fun s => by unfold AuraSrc.Simple; infer_instance

theorem AuraSrc.negates_iff {t s : AuraSrc} (ht : t.Simple) :
    t.negates s = true ↔ t.key ≠ s.key ∧
      ((t.cat = .B ∧ s.kind = .monster) ∨ ((t.cat = .A ∨ t.cat = .D) ∧ s.kind = .trap)) := by
  rw [AuraSrc.negates_eq]
  obtain ⟨h1, h2⟩ := ht
  unfold AuraSrc.cat
  cases hnt : t.nt <;> cases hnm : t.nm <;> cases hk : t.kind <;> simp_all

theorem AuraSrc.kind_A {s : AuraSrc} (h : s.cat = .A) : s.kind = .trap := by
  unfold AuraSrc.cat at h
  cases hnt : s.nt <;> cases hnm : s.nm <;> cases hk : s.kind <;> simp_all
theorem AuraSrc.kind_B {s : AuraSrc} (hs : s.Simple) (h : s.cat = .B) : s.kind = .trap := by
  unfold AuraSrc.cat at h; obtain ⟨h1, h2⟩ := hs
  cases hnt : s.nt <;> cases hnm : s.nm <;> cases hk : s.kind <;> simp_all
theorem AuraSrc.kind_D {s : AuraSrc} (hs : s.Simple) (h : s.cat = .D) : s.kind = .monster := by
  unfold AuraSrc.cat at h; obtain ⟨h1, h2⟩ := hs
  cases hnt : s.nt <;> cases hnm : s.nm <;> cases hk : s.kind <;> simp_all
theorem AuraSrc.negates_P {t s : AuraSrc} (h : t.cat = .P) : t.negates s = false := by
  rw [AuraSrc.negates_eq]; unfold AuraSrc.cat at h
  cases hnt : t.nt <;> cases hnm : t.nm <;> cases hk : t.kind <;> simp_all

theorem AuraSrc.negates_cat {t s : AuraSrc} (ht : t.Simple) (hk : t.key ≠ s.key) :
    t.negates s = ((decide (t.cat = .B) && decide (s.kind = .monster)) ||
      ((decide (t.cat = .A) || decide (t.cat = .D)) && decide (s.kind = .trap))) := by
  apply Bool.eq_iff_iff.mpr
  rw [AuraSrc.negates_iff ht]
  simp [hk]

@[simp] theorem AuraSrc.cat_on (s : AuraSrc) (b : Bool) : ({ s with on := b } : AuraSrc).cat = s.cat := rfl
@[simp] theorem AuraSrc.cat_on_since (s : AuraSrc) (b : Bool) (n : Nat) :
    ({ s with on := b, since := n } : AuraSrc).cat = s.cat := rfl

/-! ## 判定の途中の状態の量 -/

/-- 効果が適用されている：有効で、どの有効なカードにも無効にされない -/
def effIn (l : List AuraSrc) (s : AuraSrc) : Bool := s.on && !beatenIn l s

/-- j 番目のカードが p を満たす -/
def pAt (l : List AuraSrc) (j : Nat) (p : AuraSrc → Bool) : Bool := l[j]?.any p

/-- 種類 k の適用中のカードがある -/
def hasEff (l : List AuraSrc) (k : Cat) : Bool :=
  (List.range l.length).any fun j => pAt l j fun s => decide (s.cat = k) && effIn l s

def rankOf (l : List AuraSrc) : Nat :=
  if hasEff l .D then 0 else if hasEff l .A then 1 else if hasEff l .B then 2 else 3

/-- 適用されていない D・B の枚数 -/
def cntX (l : List AuraSrc) : Nat :=
  (List.range l.length).countP fun j =>
    pAt l j fun s => (decide (s.cat = .D) || decide (s.cat = .B)) && !effIn l s

/-- s は種類 k の適用中のどのカードよりも適用の時刻が古い -/
def olderThan (l : List AuraSrc) (s : AuraSrc) (k : Cat) : Bool :=
  (List.range l.length).all fun m =>
    pAt l m fun t => !(decide (t.cat = k) && effIn l t) || decide (s.since < t.since)

def cntOlder (l : List AuraSrc) (k1 k2 : Cat) : Nat :=
  (List.range l.length).countP fun j => pAt l j fun s => decide (s.cat = k1) && olderThan l s k2

def cntY (l : List AuraSrc) : Nat := cntOlder l .B .D + cntOlder l .A .A + cntOlder l .D .B

/-- 適用されていない P の枚数 -/
def cntP (l : List AuraSrc) : Nat :=
  (List.range l.length).countP fun j => pAt l j fun s => decide (s.cat = .P) && !effIn l s

/-- 有効なカードの枚数 -/
def cntOn (l : List AuraSrc) : Nat := (List.range l.length).countP fun j => pAt l j (·.on)

/-- 辞書式の順序を自然数にする（K 進数） -/
def enc (K r x y p o : Nat) : Nat := (((r * K + x) * K + y) * K + p) * K + o

def settleMeasure (l : List AuraSrc) : Nat :=
  enc (3 * l.length + 1) (rankOf l) (cntX l) (cntY l) (cntP l) (cntOn l)

/-! ### 自然数・リストの補題 -/

theorem enc_lt_of_le {K r x y p o r' x' y' p' o' : Nat} (hr : r' ≤ r) (hx : x' ≤ x) (hy : y' ≤ y)
    (hp : p' ≤ p) (ho : o' < o) : enc K r' x' y' p' o' < enc K r x y p o := by
  unfold enc
  have h1 : r' * K + x' ≤ r * K + x := Nat.add_le_add (Nat.mul_le_mul_right K hr) hx
  have h2 := Nat.add_le_add (Nat.mul_le_mul_right K h1) hy
  have h3 := Nat.add_le_add (Nat.mul_le_mul_right K h2) hp
  exact Nat.add_lt_add_of_le_of_lt (Nat.mul_le_mul_right K h3) ho

theorem lt_mul_add {K a a' b b' : Nat} (hb' : b' < K) (h : a' < a ∨ (a' = a ∧ b' < b)) :
    a' * K + b' < a * K + b := by
  rcases h with h | ⟨rfl, h⟩
  · have : (a' + 1) * K ≤ a * K := Nat.mul_le_mul_right K h
    rw [Nat.succ_mul] at this; omega
  · omega

theorem enc_lt_lex {K r x y p o r' x' y' p' o' : Nat} (hx : x' < K) (hy : y' < K) (hp : p' < K) (ho : o' < K)
    (h : r' < r ∨ (r' = r ∧ (x' < x ∨ (x' = x ∧ (y' < y ∨ (y' = y ∧ p' < p)))))) :
    enc K r' x' y' p' o' < enc K r x y p o := by
  unfold enc
  apply lt_mul_add ho; left
  rcases h with h | ⟨rfl, h | ⟨rfl, h | ⟨rfl, h⟩⟩⟩
  · exact lt_mul_add hp (.inl (lt_mul_add hy (.inl (lt_mul_add hx (.inl h)))))
  · exact lt_mul_add hp (.inl (lt_mul_add hy (.inl (lt_mul_add hx (.inr ⟨rfl, h⟩)))))
  · exact lt_mul_add hp (.inl (lt_mul_add hy (.inr ⟨rfl, h⟩)))
  · exact lt_mul_add hp (.inr ⟨rfl, h⟩)

theorem mul_add_lt {K M a b : Nat} (ha : a < M) (hb : b < K) : a * K + b < M * K := by
  have : (a + 1) * K ≤ M * K := Nat.mul_le_mul_right K ha
  rw [Nat.succ_mul] at this; omega

theorem enc_lt_bound {K r x y p o : Nat} (hx : x < K) (hy : y < K) (hp : p < K) (ho : o < K) :
    enc K r x y p o < (r + 1) * K * K * K * K := by
  unfold enc
  exact mul_add_lt (mul_add_lt (mul_add_lt (mul_add_lt (by omega) hx) hy) hp) ho

theorem countP_lt_of {α : Type} {L : List α} {p q : α → Bool} (h : ∀ x ∈ L, q x = true → p x = true)
    (hx : ∃ x ∈ L, p x = true ∧ q x = false) : L.countP q < L.countP p := by
  induction L with
  | nil => simp at hx
  | cons a L ih =>
    simp only [List.countP_cons]
    have hle : L.countP q ≤ L.countP p :=
      List.countP_mono_left fun x hx => h x (List.mem_cons_of_mem _ hx)
    obtain ⟨x, hxm, hpx, hqx⟩ := hx
    rcases List.mem_cons.mp hxm with rfl | hxm
    · simp [hpx, hqx]; omega
    · have := ih (fun y hy => h y (List.mem_cons_of_mem _ hy)) ⟨x, hxm, hpx, hqx⟩
      have ha := h a List.mem_cons_self
      cases hq : q a <;> cases hp : p a <;> simp_all <;> omega

theorem countP_range_le {n : Nat} {p q : Nat → Bool} (h : ∀ j < n, q j = true → p j = true) :
    (List.range n).countP q ≤ (List.range n).countP p :=
  List.countP_mono_left fun j hj => h j (List.mem_range.mp hj)

theorem countP_range_lt {n : Nat} {p q : Nat → Bool} (h : ∀ j < n, q j = true → p j = true)
    (hx : ∃ j < n, p j = true ∧ q j = false) : (List.range n).countP q < (List.range n).countP p :=
  countP_lt_of (fun j hj => h j (List.mem_range.mp hj))
    (let ⟨j, hj, h⟩ := hx; ⟨j, List.mem_range.mpr hj, h⟩)

theorem countP_range_eq {n : Nat} {p q : Nat → Bool} (h : ∀ j < n, q j = p j) :
    (List.range n).countP q = (List.range n).countP p :=
  List.countP_congr fun j hj => by rw [h j (List.mem_range.mp hj)]

theorem countP_range_lt_succ (n : Nat) (p : Nat → Bool) : (List.range n).countP p < n + 1 := by
  have := List.countP_le_length (p := p) (l := List.range n)
  simp at this; omega

theorem pAt_eq {l : List AuraSrc} {j : Nat} (hj : j < l.length) (p : AuraSrc → Bool) :
    pAt l j p = p l[j] := by
  simp [pAt, List.getElem?_eq_getElem hj]

theorem pAt_modify {l : List AuraSrc} {i j : Nat} {f : AuraSrc → AuraSrc} (hj : j < l.length)
    (p : AuraSrc → Bool) : pAt (l.modify i f) j p = p (if i = j then f l[j] else l[j]) := by
  simp only [pAt, List.getElem?_modify, List.getElem?_eq_getElem hj]
  simp

theorem since_lt_newestTime {l : List AuraSrc} {c : Nat} : ∀ s ∈ l, s.since < newestTime l c := by
  intro s hs; unfold newestTime
  induction l with
  | nil => simp at hs
  | cons a l ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp hs with rfl | hs
    · have := Nat.le_max_left s.since (List.foldr (fun s m => max s.since m) c l); omega
    · have := ih hs
      have := Nat.le_max_right a.since (List.foldr (fun s m => max s.since m) c l); omega

/-- `settleOnce` で変わるのは、無効にされているカードを1枚無効にするか、無効なカードを1枚有効に戻すか -/
theorem settleOnce_some {l : List AuraSrc} {c : Nat} {l' : List AuraSrc} {c' : Nat}
    (h : settleOnce l c = some (l', c')) :
    (∃ i, ∃ hi : i < l.length, l[i].on = true ∧ beatenIn l l[i] = true ∧
      l' = l.modify i (fun s => { s with on := false })) ∨
    ((∀ s ∈ l, s.on = true → beatenIn l s = false) ∧
      ∃ i, ∃ hi : i < l.length, l[i].on = false ∧ beatenIn l l[i] = false ∧
        l' = l.modify i (fun s => { s with on := true, since := newestTime l c })) := by
  unfold settleOnce at h
  split at h
  · rename_i i hi
    obtain ⟨hlt, hp, -⟩ := List.findIdx?_eq_some_iff_getElem.mp hi
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    simp only [Bool.and_eq_true] at hp
    exact .inl ⟨i, hlt, hp.1, hp.2, rfl⟩
  · rename_i hn
    split at h
    · rename_i i hi
      obtain ⟨hlt, hp, -⟩ := List.findIdx?_eq_some_iff_getElem.mp hi
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hp
      refine .inr ⟨fun s hs hon => ?_, i, hlt, hp.1, hp.2, rfl⟩
      have := List.findIdx?_eq_none_iff.mp hn s hs
      simpa [hon] using this
    · cases h

theorem rankOf_le {l l' : List AuraSrc} (h : ∀ k, hasEff l k = true → hasEff l' k = true) :
    rankOf l' ≤ rankOf l := by
  have hD := h .D; have hA := h .A; have hB := h .B
  unfold rankOf
  cases h1 : hasEff l .D <;> cases h2 : hasEff l .A <;> cases h3 : hasEff l .B <;>
    cases h1' : hasEff l' .D <;> cases h2' : hasEff l' .A <;> cases h3' : hasEff l' .B <;> simp_all

/-! ### 無効にされているカードを無効にする場合 -/

section kill
variable {l : List AuraSrc} {i : Nat}

/-- 無効にした後の有効なカードは、もとから有効 -/
theorem kill_mem {t : AuraSrc} (ht : t ∈ l.modify i (fun s => { s with on := false })) (hon : t.on = true) :
    t ∈ l := by
  obtain ⟨m, hm, rfl⟩ := List.mem_iff_getElem.mp ht
  rw [List.getElem_modify] at hon ⊢
  by_cases him : i = m
  · simp [him] at hon
  · simp [him]

theorem kill_beaten {y : AuraSrc} (h : beatenIn (l.modify i (fun s => { s with on := false })) y = true) :
    beatenIn l y = true := by
  unfold beatenIn at *
  rw [List.any_eq_true] at *
  obtain ⟨t, ht, h⟩ := h
  simp only [Bool.and_eq_true] at h
  exact ⟨t, kill_mem ht h.1, by simp [h]⟩

/-- 適用中のカードは適用中のまま -/
theorem kill_eff (hi : i < l.length) (hb : beatenIn l l[i] = true) {j : Nat} (hj : j < l.length)
    (h : effIn l l[j] = true) :
    effIn (l.modify i (fun s => { s with on := false }))
      (if i = j then { l[j] with on := false } else l[j]) = true := by
  by_cases hij : i = j
  · subst hij; simp [effIn, hb] at h
  · simp only [hij, ite_false]
    simp only [effIn, Bool.and_eq_true, Bool.not_eq_true'] at h ⊢
    refine ⟨h.1, ?_⟩
    cases hb' : beatenIn (l.modify i (fun s => { s with on := false })) l[j]
    · rfl
    · rw [kill_beaten hb'] at h; exact absurd h.2 (by simp)

theorem kill_measure (hi : i < l.length) (hon : l[i].on = true) (hb : beatenIn l l[i] = true) :
    settleMeasure (l.modify i (fun s => { s with on := false })) < settleMeasure l := by
  have hlen : (l.modify i (fun s => { s with on := false })).length = l.length := List.length_modify _ _ _
  -- 適用中のカードの種類
  have hE : ∀ k, hasEff l k = true → hasEff (l.modify i (fun s => { s with on := false })) k = true := by
    intro k h
    unfold hasEff at h ⊢
    rw [List.any_eq_true] at h ⊢
    obtain ⟨j, hj, h⟩ := h
    have hj' := List.mem_range.mp hj
    rw [pAt_eq hj'] at h
    refine ⟨j, by rw [hlen]; exact hj, ?_⟩
    rw [pAt_modify hj']
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h ⊢
    refine ⟨by split <;> simp [h.1], kill_eff hi hb hj' h.2⟩
  have hr := rankOf_le hE
  have hx : cntX (l.modify i (fun s => { s with on := false })) ≤ cntX l := by
    unfold cntX; rw [hlen]
    apply countP_range_le
    intro j hj h
    rw [pAt_modify hj] at h; rw [pAt_eq hj]
    have hc : (if i = j then { l[j] with on := false } else l[j]).cat = l[j].cat := by split <;> rfl
    have := kill_eff hi hb hj
    simp only [Bool.and_eq_true, hc] at h ⊢
    refine ⟨h.1, ?_⟩
    cases he : effIn l l[j] <;> simp_all
  have hold : ∀ k1 k2, cntOlder (l.modify i (fun s => { s with on := false })) k1 k2 ≤ cntOlder l k1 k2 := by
    intro k1 k2
    unfold cntOlder; rw [hlen]
    apply countP_range_le
    intro j hj h
    rw [pAt_modify hj] at h; rw [pAt_eq hj]
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h ⊢
    refine ⟨by split at h <;> simp_all, ?_⟩
    have h2 := h.2
    unfold olderThan at h2 ⊢
    rw [List.all_eq_true] at h2 ⊢
    intro m hm
    have hm' := List.mem_range.mp hm
    have := h2 m (by rw [hlen]; exact hm)
    rw [pAt_modify hm'] at this; rw [pAt_eq hm']
    cases he : decide (l[m].cat = k2) && effIn l l[m]
    · simp
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at he
      have he' := kill_eff hi hb hm' he.2
      have hs : (if i = j then { l[j] with on := false } else l[j]).since = l[j].since := by split <;> rfl
      have hs' : (if i = m then { l[m] with on := false } else l[m]).since = l[m].since := by split <;> rfl
      have hc : (if i = m then { l[m] with on := false } else l[m]).cat = l[m].cat := by split <;> rfl
      simp only [hc, he.1, he', decide_true, Bool.true_and, Bool.not_true, Bool.false_or, hs, hs',
        decide_eq_true_eq] at this
      simp [this]
  have hy : cntY (l.modify i (fun s => { s with on := false })) ≤ cntY l := by
    unfold cntY; have := hold .B .D; have := hold .A .A; have := hold .D .B; omega
  have hp : cntP (l.modify i (fun s => { s with on := false })) ≤ cntP l := by
    unfold cntP; rw [hlen]
    apply countP_range_le
    intro j hj h
    rw [pAt_modify hj] at h; rw [pAt_eq hj]
    have hc : (if i = j then { l[j] with on := false } else l[j]).cat = l[j].cat := by split <;> rfl
    have := kill_eff hi hb hj
    simp only [Bool.and_eq_true, hc] at h ⊢
    refine ⟨h.1, ?_⟩
    cases he : effIn l l[j] <;> simp_all
  have ho : cntOn (l.modify i (fun s => { s with on := false })) < cntOn l := by
    unfold cntOn; rw [hlen]
    apply countP_range_lt
    · intro j hj h
      rw [pAt_modify hj] at h; rw [pAt_eq hj]
      split at h
      · simp at h
      · exact h
    · refine ⟨i, hi, by rw [pAt_eq hi]; exact hon, ?_⟩
      rw [pAt_modify hi]; simp
  unfold settleMeasure; rw [hlen]
  exact enc_lt_of_le hr hx hy hp ho

end kill

/-! ### 無効なカードを有効に戻す場合 -/

/-- 時刻 T で有効に戻す -/
def AuraSrc.turnOn (s : AuraSrc) (T : Nat) : AuraSrc := { s with on := true, since := T }

@[simp] theorem AuraSrc.turnOn_on (s : AuraSrc) (T : Nat) : (s.turnOn T).on = true := rfl
@[simp] theorem AuraSrc.turnOn_since (s : AuraSrc) (T : Nat) : (s.turnOn T).since = T := rfl
@[simp] theorem AuraSrc.turnOn_cat (s : AuraSrc) (T : Nat) : (s.turnOn T).cat = s.cat := rfl
@[simp] theorem AuraSrc.turnOn_key (s : AuraSrc) (T : Nat) : (s.turnOn T).key = s.key := rfl
@[simp] theorem AuraSrc.negates_turnOn (t s : AuraSrc) (T : Nat) : t.negates (s.turnOn T) = t.negates s := by
  simp only [AuraSrc.negates_eq]; rfl
@[simp] theorem AuraSrc.turnOn_negates (t s : AuraSrc) (T : Nat) : (t.turnOn T).negates s = t.negates s := by
  simp only [AuraSrc.negates_eq]; rfl

/-- i 番目のカードを時刻 T で有効に戻したもの -/
def lOn (l : List AuraSrc) (i T : Nat) : List AuraSrc := l.modify i (·.turnOn T)

/-- x が y を一方的に無効にする -/
def uni (x y : AuraSrc) : Bool := x.negates y && !y.negates x

/-- 種類 k の適用中のカードは、i 番目を有効に戻す前と後で同じ -/
def SameE (l : List AuraSrc) (i T : Nat) (hi : i < l.length) (k : Cat) : Prop :=
  (∀ j (hj : j < l.length), j ≠ i → l[j].cat = k → l[j].on = true → uni l[i] l[j] = false) ∧
  (l[i].cat = k → effIn (lOn l i T) (l[i].turnOn T) = false)

/-- 有効に戻すときの前提 -/
structure OnCtx (l : List AuraSrc) (i T : Nat) (hi : i < l.length) : Prop where
  simple : ∀ s ∈ l, s.Simple
  nodup : (l.map (·.key)).Nodup
  off : l[i].on = false
  unb : beatenIn l l[i] = false
  kst : ∀ s ∈ l, s.on = true → beatenIn l s = false
  newer : ∀ s ∈ l, s.since < T


section turnOn
variable {l : List AuraSrc} {i T : Nat} {hi : i < l.length}

theorem lOn_length : (lOn l i T).length = l.length := List.length_modify _ _ _

theorem pAt_lOn {j : Nat} (hj : j < l.length) (p : AuraSrc → Bool) :
    pAt (lOn l i T) j p = p (if i = j then (l[j].turnOn T) else l[j]) :=
  pAt_modify hj p


theorem OnCtx.idx_of_mem {s : AuraSrc} (hs : s ∈ l) : ∃ m, ∃ hm : m < l.length, l[m] = s :=
  List.mem_iff_getElem.mp hs

theorem OnCtx.mem_lOn_of {m : Nat} (hm : m < l.length) (hmi : m ≠ i) : l[m] ∈ lOn l i T := by
  refine List.mem_iff_getElem.mpr ⟨m, by rw [lOn_length]; exact hm, ?_⟩
  unfold lOn; rw [List.getElem_modify]; simp [Ne.symm hmi]

theorem OnCtx.x_mem_lOn : (l[i].turnOn T) ∈ lOn l i T := by
  refine List.mem_iff_getElem.mpr ⟨i, by rw [lOn_length]; exact hi, ?_⟩
  unfold lOn; rw [List.getElem_modify]; simp

theorem OnCtx.mem_lOn {t : AuraSrc} (ht : t ∈ lOn l i T) :
    t = (l[i].turnOn T) ∨ ∃ m, ∃ hm : m < l.length, m ≠ i ∧ l[m] = t := by
  unfold lOn at ht
  obtain ⟨m, hm, rfl⟩ := List.mem_iff_getElem.mp ht
  have hm' : m < l.length := by simpa using hm
  rw [List.getElem_modify]
  by_cases him : i = m
  · subst him; left; simp
  · right; exact ⟨m, hm', Ne.symm him, by simp [him]⟩

namespace OnCtx
variable (C : OnCtx l i T hi)
include C

/-- 有効なカードは i 番目ではない -/
theorem ne_of_on {m : Nat} (hm : m < l.length) (hon : l[m].on = true) : m ≠ i := by
  rintro rfl; rw [C.off] at hon; cases hon


theorem key_ne {j : Nat} (hj : j < l.length) (hji : j ≠ i) : l[j].key ≠ l[i].key := by
  intro h
  have := C.nodup.getElem_inj (i := j) (j := i) (hi := by simp; exact hj) (hj := by simp; exact hi)
  simp only [List.getElem_map] at this
  exact hji (this.mp h)

/-- 有効に戻すカードを無効にする、有効なカードはない（一方的に無効にするものはない） -/
theorem unb' {s : AuraSrc} (hs : s ∈ l) (hon : s.on = true) (hn : s.negates l[i] = true) :
    l[i].negates s = true ∧ l[i].since < s.since := by
  have h := C.unb
  unfold beatenIn at h
  rw [List.any_eq_false] at h
  have := h s hs
  simp only [hon, AuraSrc.beats, hn, Bool.true_and] at this
  simpa using this

/-- 有効なカード同士は無効にし合わない -/
theorem free {s t : AuraSrc} (hs : s ∈ l) (ht : t ∈ l) (hso : s.on = true) (hto : t.on = true) :
    t.negates s = false := by
  have h1 := C.kst s hs hso
  have h2 := C.kst t ht hto
  unfold beatenIn at h1 h2
  rw [List.any_eq_false] at h1 h2
  have a : t.beats s = false := by simpa [hto] using h1 t ht
  have b : s.beats t = false := by simpa [hso] using h2 s hs
  unfold AuraSrc.beats at a b
  cases hn : t.negates s <;> cases hn' : s.negates t <;> simp_all <;> omega

theorem beats_x' {y : AuraSrc} (hy : y ∈ l) :
    (l[i].turnOn T).beats y = uni l[i] y := by
  have := C.newer y hy
  simp only [AuraSrc.beats, uni, AuraSrc.turnOn_negates, AuraSrc.negates_turnOn, AuraSrc.turnOn_since]
  have h' : ¬ T < y.since := by omega
  cases y.negates l[i] <;> simp [this]

/-- 有効に戻した後、i 番目以外のカードが無効にされているか -/
theorem beaten_lOn {j : Nat} (hj : j < l.length) :
    beatenIn (lOn l i T) l[j] = (uni l[i] l[j] || beatenIn l l[j]) := by
  rw [← C.beats_x' (List.getElem_mem hj)]
  apply Bool.eq_iff_iff.mpr
  simp only [beatenIn, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true]
  constructor
  · rintro ⟨t, ht, hto, hb⟩
    rcases OnCtx.mem_lOn (hi := hi) ht with h | ⟨m, hm, -, rfl⟩
    · rw [h] at hb; exact .inl hb
    · exact .inr ⟨l[m], List.getElem_mem hm, hto, hb⟩
  · rintro (hb | ⟨t, ht, hto, hb⟩)
    · exact ⟨_, OnCtx.x_mem_lOn, rfl, hb⟩
    · obtain ⟨m, hm, rfl⟩ := OnCtx.idx_of_mem ht
      exact ⟨l[m], OnCtx.mem_lOn_of hm (C.ne_of_on hm hto), hto, hb⟩

/-- 有効に戻したカードが無効にされているか -/
theorem beaten_x' :
    beatenIn (lOn l i T) (l[i].turnOn T) = true ↔
      ∃ s ∈ l, s.on = true ∧ s.negates l[i] = true := by
  simp only [beatenIn, List.any_eq_true, Bool.and_eq_true]
  constructor
  · rintro ⟨t, ht, hto, hb⟩
    rcases OnCtx.mem_lOn (hi := hi) ht with h | ⟨m, hm, hmi, rfl⟩
    · rw [h] at hb; simp [AuraSrc.beats, AuraSrc.negates_eq] at hb
    · refine ⟨l[m], List.getElem_mem hm, hto, ?_⟩
      simp only [AuraSrc.beats, AuraSrc.negates_turnOn, Bool.and_eq_true] at hb
      exact hb.1
  · rintro ⟨s, hs, hso, hn⟩
    obtain ⟨m, hm, rfl⟩ := OnCtx.idx_of_mem hs
    refine ⟨l[m], OnCtx.mem_lOn_of hm (C.ne_of_on hm hso), hso, ?_⟩
    have := C.newer _ hs
    simp only [AuraSrc.beats, AuraSrc.negates_turnOn, AuraSrc.turnOn_negates, AuraSrc.turnOn_since, hn,
      Bool.true_and]
    have h' : ¬ T < l[m].since := by omega
    simp [h']

theorem eff_l {s : AuraSrc} (hs : s ∈ l) : effIn l s = s.on := by
  unfold effIn
  cases h : s.on
  · rfl
  · simp [C.kst s hs h]

theorem eff_lOn {j : Nat} (hj : j < l.length) :
    effIn (lOn l i T) l[j] = (l[j].on && !uni l[i] l[j]) := by
  unfold effIn
  rw [C.beaten_lOn hj]
  cases h : l[j].on
  · rfl
  · simp [C.kst _ (List.getElem_mem hj) h]

theorem eff_x' :
    effIn (lOn l i T) (l[i].turnOn T) = true ↔ ¬∃ s ∈ l, s.on = true ∧ s.negates l[i] = true := by
  rw [← C.beaten_x']
  simp [effIn]

omit C in
theorem pAt_lOn_ne {j : Nat} (hj : j < l.length) (hji : j ≠ i) (p : AuraSrc → Bool) :
    pAt (lOn l i T) j p = p l[j] := by
  rw [pAt_lOn hj]; simp [Ne.symm hji]

omit C in
theorem pAt_lOn_i (p : AuraSrc → Bool) : pAt (lOn l i T) i p = p (l[i].turnOn T) := by
  rw [pAt_lOn hi]; simp

/-! #### 適用中の種類 -/

theorem hasEff_l {k : Cat} : hasEff l k = true ↔ ∃ s ∈ l, s.cat = k ∧ s.on = true := by
  unfold hasEff
  simp only [List.any_eq_true, List.mem_range]
  constructor
  · rintro ⟨j, hj, h⟩
    rw [pAt_eq hj] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨l[j], List.getElem_mem hj, h.1, by rw [← C.eff_l (List.getElem_mem hj)]; exact h.2⟩
  · rintro ⟨s, hs, hc, hon⟩
    obtain ⟨j, hj, rfl⟩ := OnCtx.idx_of_mem hs
    refine ⟨j, hj, ?_⟩
    rw [pAt_eq hj, C.eff_l (List.getElem_mem hj)]
    simp [hc, hon]

theorem hasEff_lOn_of_idx {k : Cat} {m : Nat} (hm : m < l.length) (hmi : m ≠ i) (hc : l[m].cat = k)
    (hon : l[m].on = true) (hu : uni l[i] l[m] = false) : hasEff (lOn l i T) k = true := by
  unfold hasEff
  simp only [List.any_eq_true, List.mem_range, lOn_length]
  refine ⟨m, hm, ?_⟩
  rw [pAt_lOn_ne hm hmi, C.eff_lOn hm]
  simp [hc, hon, hu]

omit C in
theorem hasEff_lOn_of_x {k : Cat} (hc : l[i].cat = k) (he : effIn (lOn l i T) (l[i].turnOn T) = true) :
    hasEff (lOn l i T) k = true := by
  unfold hasEff
  simp only [List.any_eq_true, List.mem_range, lOn_length]
  refine ⟨i, hi, ?_⟩
  rw [pAt_lOn_i (hi := hi)]
  simp [hc, he]

theorem hasEff_lOn_false {k : Cat} (hno : ∀ s ∈ l, s.cat = k → s.on = false)
    (hx : l[i].cat = k → effIn (lOn l i T) (l[i].turnOn T) = false) : hasEff (lOn l i T) k = false := by
  unfold hasEff
  simp only [List.any_eq_false, List.mem_range, lOn_length]
  intro j hj
  by_cases hji : j = i
  · subst hji; rw [pAt_lOn_i (hi := hi)]
    by_cases hc : l[j].cat = k
    · simp [hx hc]
    · simp [hc]
  · rw [pAt_lOn_ne hj hji, C.eff_lOn hj]
    by_cases hc : l[j].cat = k
    · simp [hno _ (List.getElem_mem hj) hc]
    · simp [hc]

/-! #### 適用されていないカードの枚数 -/

/-- 種類が q を満たす、適用されていないカードの枚数 -/
def _root_.YGO.cntNE (l : List AuraSrc) (q : Cat → Bool) : Nat :=
  (List.range l.length).countP fun j => pAt l j fun s => q s.cat && !effIn l s

theorem cntNE_pt {q : Cat → Bool}
    (hno : ∀ j (hj : j < l.length), j ≠ i → q l[j].cat = true → l[j].on = true → uni l[i] l[j] = false)
    {j : Nat} (hj : j < l.length) (hji : j ≠ i) :
    pAt (lOn l i T) j (fun s => q s.cat && !effIn (lOn l i T) s) = pAt l j (fun s => q s.cat && !effIn l s) := by
  rw [pAt_lOn_ne hj hji, pAt_eq hj, C.eff_lOn hj, C.eff_l (List.getElem_mem hj)]
  cases hq : q l[j].cat
  · simp
  · cases hon : l[j].on
    · simp
    · simp [hno j hj hji hq hon]

theorem cntNE_eq {q : Cat → Bool}
    (hno : ∀ j (hj : j < l.length), j ≠ i → q l[j].cat = true → l[j].on = true → uni l[i] l[j] = false)
    (hx : q l[i].cat = true → effIn (lOn l i T) (l[i].turnOn T) = false) :
    cntNE (lOn l i T) q = cntNE l q := by
  unfold cntNE; rw [lOn_length]
  apply countP_range_eq
  intro j hj
  by_cases hji : j = i
  · subst hji
    rw [pAt_lOn_i (hi := hi), pAt_eq hj, C.eff_l (List.getElem_mem hj), C.off]
    simp only [AuraSrc.turnOn_cat]
    cases hq : q l[j].cat
    · simp
    · simp [hx hq]
  · exact C.cntNE_pt hno hj hji

theorem cntNE_lt {q : Cat → Bool}
    (hno : ∀ j (hj : j < l.length), j ≠ i → q l[j].cat = true → l[j].on = true → uni l[i] l[j] = false)
    (hq : q l[i].cat = true) (he : effIn (lOn l i T) (l[i].turnOn T) = true) :
    cntNE (lOn l i T) q < cntNE l q := by
  unfold cntNE; rw [lOn_length]
  apply countP_range_lt
  · intro j hj h
    by_cases hji : j = i
    · subst hji
      rw [pAt_eq hj, C.eff_l (List.getElem_mem hj), C.off]
      simp [hq]
    · rw [← C.cntNE_pt hno hj hji]; exact h
  · refine ⟨i, hi, ?_, ?_⟩
    · rw [pAt_eq hi, C.eff_l (List.getElem_mem hi), C.off]; simp [hq]
    · rw [pAt_lOn_i (hi := hi)]; simp [he]

/-! #### 時刻の古いカードの枚数 -/

theorem olderThan_eq {k : Cat} (hS : SameE l i T hi k) (s : AuraSrc) :
    olderThan (lOn l i T) s k = olderThan l s k := by
  unfold olderThan; rw [lOn_length]
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_eq_true, List.mem_range]
  apply forall_congr'; intro m; apply forall_congr'; intro hm
  by_cases hmi : m = i
  · subst hmi
    rw [pAt_lOn_i (hi := hi), pAt_eq hm, C.eff_l (List.getElem_mem hm), C.off]
    by_cases hc : l[m].cat = k
    · simp [hS.2 hc]
    · simp [hc]
  · rw [pAt_lOn_ne hm hmi, pAt_eq hm, C.eff_lOn hm, C.eff_l (List.getElem_mem hm)]
    by_cases hc : l[m].cat = k
    · cases hon : l[m].on
      · simp
      · simp [hS.1 m hm hmi hc hon]
    · simp [hc]

theorem cntOlder_eq {k1 k2 : Cat} (hS : SameE l i T hi k2) (hx : l[i].cat ≠ k1) :
    cntOlder (lOn l i T) k1 k2 = cntOlder l k1 k2 := by
  unfold cntOlder; rw [lOn_length]
  apply countP_range_eq
  intro j hj
  by_cases hji : j = i
  · subst hji; rw [pAt_lOn_i (hi := hi), pAt_eq hj]; simp [hx]
  · rw [pAt_lOn_ne hj hji, pAt_eq hj, C.olderThan_eq hS]

theorem cntOlder_lt {k1 k2 : Cat} (hS : SameE l i T hi k2) (hx : l[i].cat = k1)
    (hold : ∀ s ∈ l, s.cat = k2 → s.on = true → l[i].since < s.since)
    {m : Nat} (hm : m < l.length) (hmi : m ≠ i) (hmc : l[m].cat = k2) (hmo : l[m].on = true)
    (hmu : uni l[i] l[m] = false) :
    cntOlder (lOn l i T) k1 k2 < cntOlder l k1 k2 := by
  unfold cntOlder; rw [lOn_length]
  apply countP_range_lt
  · intro j hj h
    by_cases hji : j = i
    · subst hji
      rw [pAt_eq hj]
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨hx, ?_⟩
      unfold olderThan
      simp only [List.all_eq_true, List.mem_range]
      intro m' hm'
      rw [pAt_eq hm', C.eff_l (List.getElem_mem hm')]
      by_cases hc : l[m'].cat = k2
      · cases hon : l[m'].on
        · simp
        · simp [hold _ (List.getElem_mem hm') hc hon]
      · simp [hc]
    · rw [pAt_lOn_ne hj hji, C.olderThan_eq hS] at h; rw [pAt_eq hj]; exact h
  · refine ⟨i, hi, ?_, ?_⟩
    · rw [pAt_eq hi]
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨hx, ?_⟩
      unfold olderThan
      simp only [List.all_eq_true, List.mem_range]
      intro m' hm'
      rw [pAt_eq hm', C.eff_l (List.getElem_mem hm')]
      by_cases hc : l[m'].cat = k2
      · cases hon : l[m'].on
        · simp
        · simp [hold _ (List.getElem_mem hm') hc hon]
      · simp [hc]
    · rw [pAt_lOn_i (hi := hi)]
      simp only [AuraSrc.turnOn_cat, hx, decide_true, Bool.true_and]
      unfold olderThan
      simp only [List.all_eq_false, List.mem_range, lOn_length]
      refine ⟨m, hm, ?_⟩
      rw [pAt_lOn_ne hm hmi, C.eff_lOn hm]
      have := C.newer _ (List.getElem_mem hm)
      have h' : ¬ T < l[m].since := by omega
      simp [hmc, hmo, hmu, h']

/-! #### 種類ごとの場合分け -/

theorem simple_idx {j : Nat} (hj : j < l.length) : l[j].Simple := C.simple _ (List.getElem_mem hj)

theorem key_inj {s t : AuraSrc} (hs : s ∈ l) (ht : t ∈ l) (h : s.key = t.key) : s = t := by
  obtain ⟨a, ha, rfl⟩ := OnCtx.idx_of_mem hs
  obtain ⟨b, hb, rfl⟩ := OnCtx.idx_of_mem ht
  have := C.nodup.getElem_inj (i := a) (j := b) (hi := by simp; exact ha) (hj := by simp; exact hb)
  simp only [List.getElem_map] at this
  obtain rfl := this.mp h; rfl

theorem key_ne_of_cat {s t : AuraSrc} (hs : s ∈ l) (ht : t ∈ l) (hc : s.cat ≠ t.cat) : s.key ≠ t.key :=
  fun h => hc (by rw [C.key_inj hs ht h])

theorem key_ne_on {s : AuraSrc} (hs : s ∈ l) (hon : s.on = true) : s.key ≠ l[i].key := by
  obtain ⟨m, hm, rfl⟩ := OnCtx.idx_of_mem hs
  exact C.key_ne hm (C.ne_of_on hm hon)

theorem hasEff_lOn_eq {k : Cat}
    (hu : ∀ j (hj : j < l.length), j ≠ i → l[j].cat = k → l[j].on = true → uni l[i] l[j] = false)
    (hx : l[i].cat ≠ k) : hasEff (lOn l i T) k = hasEff l k := by
  cases h : hasEff l k
  · apply C.hasEff_lOn_false
    · intro s hs hc
      cases hon : s.on
      · rfl
      · have := C.hasEff_l.mpr ⟨s, hs, hc, hon⟩; rw [h] at this; cases this
    · intro hc; exact absurd hc hx
  · obtain ⟨s, hs, hc, hon⟩ := C.hasEff_l.mp h
    obtain ⟨m, hm, rfl⟩ := OnCtx.idx_of_mem hs
    exact C.hasEff_lOn_of_idx hm (C.ne_of_on hm hon) hc hon (hu m hm (C.ne_of_on hm hon) hc hon)

omit C in
theorem noOn_of {k : Cat} (h : ¬∃ s ∈ l, s.cat = k ∧ s.on = true) : ∀ s ∈ l, s.cat = k → s.on = false := by
  intro s hs hc
  cases hon : s.on
  · rfl
  · exact absurd ⟨s, hs, hc, hon⟩ h

theorem hasEff_false_of {k : Cat} (h : ∀ s ∈ l, s.cat = k → s.on = false) : hasEff l k = false := by
  cases hh : hasEff l k
  · rfl
  · obtain ⟨s, hs, hc, hon⟩ := C.hasEff_l.mp hh
    rw [h s hs hc] at hon; cases hon

omit C in
theorem cntX_eq_cntNE (l : List AuraSrc) : cntX l = cntNE l (fun c => decide (c = .D) || decide (c = .B)) := rfl
omit C in
theorem cntP_eq_cntNE (l : List AuraSrc) : cntP l = cntNE l (fun c => decide (c = .P)) := rfl

/-- **有効に戻すと、量が減る** -/
theorem measure_lt : settleMeasure (lOn l i T) < settleMeasure l := by
  have hxS := C.simple_idx hi
  have hlen : (lOn l i T).length = l.length := lOn_length
  have bX : cntX (lOn l i T) < 3 * l.length + 1 := by
    have := countP_range_lt_succ (lOn l i T).length
      (fun j => pAt (lOn l i T) j fun s => (decide (s.cat = .D) || decide (s.cat = .B)) && !effIn (lOn l i T) s)
    unfold cntX; omega
  have bP : cntP (lOn l i T) < 3 * l.length + 1 := by
    have := countP_range_lt_succ (lOn l i T).length
      (fun j => pAt (lOn l i T) j fun s => decide (s.cat = .P) && !effIn (lOn l i T) s)
    unfold cntP; omega
  have bO : cntOn (lOn l i T) < 3 * l.length + 1 := by
    have := countP_range_lt_succ (lOn l i T).length (fun j => pAt (lOn l i T) j (·.on))
    unfold cntOn; omega
  have bY : cntY (lOn l i T) < 3 * l.length + 1 := by
    have h1 := countP_range_lt_succ (lOn l i T).length
      (fun j => pAt (lOn l i T) j fun s => decide (s.cat = .B) && olderThan (lOn l i T) s .D)
    have h2 := countP_range_lt_succ (lOn l i T).length
      (fun j => pAt (lOn l i T) j fun s => decide (s.cat = .A) && olderThan (lOn l i T) s .A)
    have h3 := countP_range_lt_succ (lOn l i T).length
      (fun j => pAt (lOn l i T) j fun s => decide (s.cat = .D) && olderThan (lOn l i T) s .B)
    unfold cntY cntOlder; omega
  unfold settleMeasure; rw [hlen]
  apply enc_lt_lex bX bY bP bO
  -- 有効なカードの性質
  cases hxc : l[i].cat with
  | P =>
    -- 何も無効にしないカード：適用中になるだけ
    have hu : ∀ y, uni l[i] y = false := fun y => by simp [uni, AuraSrc.negates_P hxc]
    have he : effIn (lOn l i T) (l[i].turnOn T) = true := by
      rw [C.eff_x']
      rintro ⟨s, hs, hon, hn⟩
      have := (C.unb' hs hon hn).1
      rw [AuraSrc.negates_P hxc] at this; cases this
    have hr : rankOf (lOn l i T) = rankOf l := by
      unfold rankOf
      rw [C.hasEff_lOn_eq (k := .D) (fun _ _ _ _ _ => hu _) (by simp [hxc]),
        C.hasEff_lOn_eq (k := .A) (fun _ _ _ _ _ => hu _) (by simp [hxc]),
        C.hasEff_lOn_eq (k := .B) (fun _ _ _ _ _ => hu _) (by simp [hxc])]
    have hS : ∀ k, k ≠ .P → SameE l i T hi k := fun k hk =>
      ⟨fun _ _ _ _ _ => hu _, fun hc => by rw [hxc] at hc; exact absurd hc.symm hk⟩
    have hx : cntX (lOn l i T) = cntX l := by
      rw [cntX_eq_cntNE, cntX_eq_cntNE]
      exact C.cntNE_eq (fun _ _ _ _ _ => hu _) (by simp [hxc])
    have hy : cntY (lOn l i T) = cntY l := by
      unfold cntY
      rw [C.cntOlder_eq (hS .D (by simp)) (by simp [hxc]), C.cntOlder_eq (hS .A (by simp)) (by simp [hxc]),
        C.cntOlder_eq (hS .B (by simp)) (by simp [hxc])]
    have hp : cntP (lOn l i T) < cntP l := by
      rw [cntP_eq_cntNE, cntP_eq_cntNE]
      exact C.cntNE_lt (fun _ _ _ _ _ => hu _) (by simp [hxc]) he
    exact .inr ⟨hr, .inr ⟨hx, .inr ⟨hy, hp⟩⟩⟩
  | D =>
    -- 罠を無効にするモンスター（サイコ・ショッカー）
    have hxk : l[i].kind = .monster := AuraSrc.kind_D hxS hxc
    have hneg : ∀ s ∈ l, s.on = true → s.negates l[i] = true → s.cat = .B := by
      intro s hs hon hn
      rw [AuraSrc.negates_cat (C.simple s hs) (C.key_ne_on hs hon), hxk] at hn
      cases hc : s.cat <;> simp_all
    have huD : ∀ j (hj : j < l.length), j ≠ i → l[j].cat = .D → uni l[i] l[j] = false := by
      intro j hj hji hc
      have hk := C.key_ne hj hji
      simp [uni, AuraSrc.negates_cat hxS (Ne.symm hk), hxc, AuraSrc.kind_D (C.simple_idx hj) hc]
    have huB : ∀ j (hj : j < l.length), j ≠ i → l[j].cat = .B → uni l[i] l[j] = false := by
      intro j hj hji hc
      have hk := C.key_ne hj hji
      simp [uni, AuraSrc.negates_cat (C.simple_idx hj) hk, hc, hxk]
    have huDB : ∀ j (hj : j < l.length), j ≠ i → (decide (l[j].cat = .D) || decide (l[j].cat = .B)) = true →
        l[j].on = true → uni l[i] l[j] = false := by
      intro j hj hji hc _
      simp only [Bool.or_eq_true, decide_eq_true_eq] at hc
      rcases hc with hc | hc
      · exact huD j hj hji hc
      · exact huB j hj hji hc
    by_cases hB : ∃ s ∈ l, s.cat = .B ∧ s.on = true
    · -- 先に適用中の B に、すぐまた無効にされる
      obtain ⟨b, hb, hbc, hbo⟩ := hB
      obtain ⟨m, hm, rfl⟩ := OnCtx.idx_of_mem hb
      have hmi := C.ne_of_on hm hbo
      have hbS := C.simple_idx hm
      have hbk := C.key_ne hm hmi
      have hbx : l[m].negates l[i] = true := by simp [AuraSrc.negates_cat hbS hbk, hbc, hxk]
      have he : effIn (lOn l i T) (l[i].turnOn T) = false := by
        cases h : effIn (lOn l i T) (l[i].turnOn T)
        · rfl
        · exact absurd ⟨l[m], hb, hbo, hbx⟩ ((C.eff_x').mp h)
      have noD : ∀ s ∈ l, s.cat = .D → s.on = false := by
        intro s hs hc
        cases hon : s.on
        · rfl
        · have h := C.free hs hb hon hbo
          have hk := C.key_ne_of_cat hb hs (by rw [hbc, hc]; decide)
          rw [AuraSrc.negates_cat hbS hk, hbc, AuraSrc.kind_D (C.simple s hs) hc] at h
          simp at h
      have noA : ∀ s ∈ l, s.cat = .A → s.on = false := by
        intro s hs hc
        cases hon : s.on
        · rfl
        · have h := C.free hb hs hbo hon
          have hk := C.key_ne_of_cat hs hb (by rw [hbc, hc]; decide)
          rw [AuraSrc.negates_cat (C.simple s hs) hk, hc, AuraSrc.kind_B hbS hbc] at h
          simp at h
      have hr : rankOf (lOn l i T) = rankOf l := by
        unfold rankOf
        rw [C.hasEff_false_of noD, C.hasEff_false_of noA,
          C.hasEff_lOn_false noD (fun _ => he), C.hasEff_lOn_false noA (fun h => by rw [hxc] at h; cases h),
          C.hasEff_lOn_of_idx hm hmi hbc hbo (huB m hm hmi hbc), C.hasEff_l.mpr ⟨l[m], hb, hbc, hbo⟩]
      have hx : cntX (lOn l i T) = cntX l := by
        rw [cntX_eq_cntNE, cntX_eq_cntNE]
        exact C.cntNE_eq huDB (fun _ => he)
      have hy : cntY (lOn l i T) < cntY l := by
        unfold cntY
        have h1 := C.cntOlder_eq (k1 := .B) (k2 := .D) ⟨fun j hj hji hc _ => huD j hj hji hc, fun _ => he⟩
          (by simp [hxc])
        have h2 := C.cntOlder_eq (k1 := .A) (k2 := .A)
          ⟨fun j hj _ hc hon => (by rw [noA _ (List.getElem_mem hj) hc] at hon; cases hon),
           fun h => (by rw [hxc] at h; cases h)⟩ (by simp [hxc])
        have h3 := C.cntOlder_lt (k1 := .D) (k2 := .B)
          ⟨fun j hj hji hc _ => huB j hj hji hc, fun h => (by rw [hxc] at h; cases h)⟩ hxc
          (fun s hs hc hon => (C.unb' hs hon
            (by simp [AuraSrc.negates_cat (C.simple s hs) (C.key_ne_on hs hon), hc, hxk])).2)
          hm hmi hbc hbo (huB m hm hmi hbc)
        omega
      exact .inr ⟨hr, .inr ⟨hx, .inl hy⟩⟩
    · -- 適用中になる
      have noB := noOn_of hB
      have he : effIn (lOn l i T) (l[i].turnOn T) = true := by
        rw [C.eff_x']
        rintro ⟨s, hs, hon, hn⟩
        have := noB s hs (hneg s hs hon hn); rw [hon] at this; cases this
      have hD' : hasEff (lOn l i T) .D = true := hasEff_lOn_of_x hxc he
      have hr' : rankOf (lOn l i T) = 0 := by simp [rankOf, hD']
      cases hD : hasEff l .D
      · left; rw [hr']; unfold rankOf; simp only [hD, Bool.false_eq_true, ite_false]
        split <;> (try split) <;> omega
      · right; refine ⟨by rw [hr']; simp [rankOf, hD], .inl ?_⟩
        rw [cntX_eq_cntNE, cntX_eq_cntNE]
        exact C.cntNE_lt huDB (by simp [hxc]) he
  | B =>
    -- モンスターを無効にする罠（スキルドレイン）
    have hxk : l[i].kind = .trap := AuraSrc.kind_B hxS hxc
    have hneg : ∀ s ∈ l, s.on = true → s.negates l[i] = true → s.cat = .A ∨ s.cat = .D := by
      intro s hs hon hn
      rw [AuraSrc.negates_cat (C.simple s hs) (C.key_ne_on hs hon), hxk] at hn
      cases hc : s.cat <;> simp_all
    have huD : ∀ j (hj : j < l.length), j ≠ i → l[j].cat = .D → uni l[i] l[j] = false := by
      intro j hj hji hc
      have hk := C.key_ne hj hji
      simp [uni, AuraSrc.negates_cat (C.simple_idx hj) hk, hc, hxk]
    have huB : ∀ j (hj : j < l.length), j ≠ i → l[j].cat = .B → uni l[i] l[j] = false := by
      intro j hj hji hc
      have hk := C.key_ne hj hji
      simp [uni, AuraSrc.negates_cat hxS (Ne.symm hk), hxc, AuraSrc.kind_B (C.simple_idx hj) hc]
    have huA : ∀ j (hj : j < l.length), j ≠ i → l[j].cat = .A → uni l[i] l[j] = false := by
      intro j hj hji hc
      have hk := C.key_ne hj hji
      simp [uni, AuraSrc.negates_cat hxS (Ne.symm hk), hxc, AuraSrc.kind_A hc]
    have huDB : ∀ j (hj : j < l.length), j ≠ i → (decide (l[j].cat = .D) || decide (l[j].cat = .B)) = true →
        l[j].on = true → uni l[i] l[j] = false := by
      intro j hj hji hc _
      simp only [Bool.or_eq_true, decide_eq_true_eq] at hc
      rcases hc with hc | hc
      · exact huD j hj hji hc
      · exact huB j hj hji hc
    -- 有効な A があれば、有効に戻せなかったはず
    have noA : ∀ s ∈ l, s.cat = .A → s.on = false := by
      intro s hs hc
      cases hon : s.on
      · rfl
      · have h := (C.unb' hs hon (by
          simp [AuraSrc.negates_cat (C.simple s hs) (C.key_ne_on hs hon), hc, hxk])).1
        rw [AuraSrc.negates_cat hxS (Ne.symm (C.key_ne_on hs hon)), hxc, AuraSrc.kind_A hc] at h
        simp at h
    by_cases hD : ∃ s ∈ l, s.cat = .D ∧ s.on = true
    · -- 先に適用中の D に、すぐまた無効にされる
      obtain ⟨d, hd, hdc, hdo⟩ := hD
      obtain ⟨m, hm, rfl⟩ := OnCtx.idx_of_mem hd
      have hmi := C.ne_of_on hm hdo
      have hdk := C.key_ne hm hmi
      have hdx : l[m].negates l[i] = true := by simp [AuraSrc.negates_cat (C.simple_idx hm) hdk, hdc, hxk]
      have he : effIn (lOn l i T) (l[i].turnOn T) = false := by
        cases h : effIn (lOn l i T) (l[i].turnOn T)
        · rfl
        · exact absurd ⟨l[m], hd, hdo, hdx⟩ ((C.eff_x').mp h)
      have hr : rankOf (lOn l i T) = rankOf l := by
        simp [rankOf, C.hasEff_lOn_of_idx hm hmi hdc hdo (huD m hm hmi hdc),
          C.hasEff_l.mpr ⟨l[m], hd, hdc, hdo⟩]
      have hx : cntX (lOn l i T) = cntX l := by
        rw [cntX_eq_cntNE, cntX_eq_cntNE]
        exact C.cntNE_eq huDB (fun _ => he)
      have hy : cntY (lOn l i T) < cntY l := by
        unfold cntY
        have h1 := C.cntOlder_lt (k1 := .B) (k2 := .D)
          ⟨fun j hj hji hc _ => huD j hj hji hc, fun h => (by rw [hxc] at h; cases h)⟩ hxc
          (fun s hs hc hon => (C.unb' hs hon
            (by simp [AuraSrc.negates_cat (C.simple s hs) (C.key_ne_on hs hon), hc, hxk])).2)
          hm hmi hdc hdo (huD m hm hmi hdc)
        have h2 := C.cntOlder_eq (k1 := .A) (k2 := .A)
          ⟨fun j hj hji hc _ => huA j hj hji hc, fun h => (by rw [hxc] at h; cases h)⟩ (by simp [hxc])
        have h3 := C.cntOlder_eq (k1 := .D) (k2 := .B)
          ⟨fun j hj hji hc _ => huB j hj hji hc, fun _ => he⟩ (by simp [hxc])
        omega
      exact .inr ⟨hr, .inr ⟨hx, .inl hy⟩⟩
    · -- 適用中になる
      have noD := noOn_of hD
      have he : effIn (lOn l i T) (l[i].turnOn T) = true := by
        rw [C.eff_x']
        rintro ⟨s, hs, hon, hn⟩
        rcases hneg s hs hon hn with hc | hc
        · have := noA s hs hc; rw [hon] at this; cases this
        · have := noD s hs hc; rw [hon] at this; cases this
      have hr' : rankOf (lOn l i T) = 2 := by
        simp [rankOf, C.hasEff_lOn_false noD (fun h => by rw [hxc] at h; cases h),
          C.hasEff_lOn_false noA (fun h => by rw [hxc] at h; cases h), hasEff_lOn_of_x hxc he]
      cases hB : hasEff l .B
      · left; rw [hr']
        simp [rankOf, C.hasEff_false_of noD, C.hasEff_false_of noA, hB]
      · right
        refine ⟨by rw [hr']; simp [rankOf, C.hasEff_false_of noD, C.hasEff_false_of noA, hB], .inl ?_⟩
        rw [cntX_eq_cntNE, cntX_eq_cntNE]
        exact C.cntNE_lt huDB (by simp [hxc]) he
  | A =>
    -- 罠を無効にする罠（王宮のお触れ）
    have hxk : l[i].kind = .trap := AuraSrc.kind_A hxc
    have hneg : ∀ s ∈ l, s.on = true → s.negates l[i] = true → s.cat = .A ∨ s.cat = .D := by
      intro s hs hon hn
      rw [AuraSrc.negates_cat (C.simple s hs) (C.key_ne_on hs hon), hxk] at hn
      cases hc : s.cat <;> simp_all
    have huA : ∀ j (hj : j < l.length), j ≠ i → l[j].cat = .A → uni l[i] l[j] = false := by
      intro j hj hji hc
      have hk := C.key_ne hj hji
      simp [uni, AuraSrc.negates_cat (C.simple_idx hj) hk, hc, hxk]
    have huD : ∀ j (hj : j < l.length), j ≠ i → l[j].cat = .D → uni l[i] l[j] = false := by
      intro j hj hji hc
      have hk := C.key_ne hj hji
      simp [uni, AuraSrc.negates_cat hxS (Ne.symm hk), hxc, AuraSrc.kind_D (C.simple_idx hj) hc]
    -- 有効な D があれば、有効に戻せなかったはず
    have noD : ∀ s ∈ l, s.cat = .D → s.on = false := by
      intro s hs hc
      cases hon : s.on
      · rfl
      · have h := (C.unb' hs hon (by
          simp [AuraSrc.negates_cat (C.simple s hs) (C.key_ne_on hs hon), hc, hxk])).1
        rw [AuraSrc.negates_cat hxS (Ne.symm (C.key_ne_on hs hon)), hxc,
          AuraSrc.kind_D (C.simple s hs) hc] at h
        simp at h
    by_cases hA : ∃ s ∈ l, s.cat = .A ∧ s.on = true
    · -- 先に適用中の A に、すぐまた無効にされる
      obtain ⟨a, ha, hac, hao⟩ := hA
      obtain ⟨m, hm, rfl⟩ := OnCtx.idx_of_mem ha
      have hmi := C.ne_of_on hm hao
      have hak := C.key_ne hm hmi
      have haS := C.simple_idx hm
      have hax : l[m].negates l[i] = true := by simp [AuraSrc.negates_cat haS hak, hac, hxk]
      have he : effIn (lOn l i T) (l[i].turnOn T) = false := by
        cases h : effIn (lOn l i T) (l[i].turnOn T)
        · rfl
        · exact absurd ⟨l[m], ha, hao, hax⟩ ((C.eff_x').mp h)
      have noB : ∀ s ∈ l, s.cat = .B → s.on = false := by
        intro s hs hc
        cases hon : s.on
        · rfl
        · have h := C.free hs ha hon hao
          have hk := C.key_ne_of_cat ha hs (by rw [hac, hc]; decide)
          rw [AuraSrc.negates_cat haS hk, hac, AuraSrc.kind_B (C.simple s hs) hc] at h
          simp at h
      have hr : rankOf (lOn l i T) = rankOf l := by
        simp [rankOf, C.hasEff_false_of noD, C.hasEff_lOn_false noD (fun h => by rw [hxc] at h; cases h),
          C.hasEff_lOn_of_idx hm hmi hac hao (huA m hm hmi hac), C.hasEff_l.mpr ⟨l[m], ha, hac, hao⟩]
      have hx : cntX (lOn l i T) = cntX l := by
        rw [cntX_eq_cntNE, cntX_eq_cntNE]
        refine C.cntNE_eq (fun j hj hji hc hon => ?_) (fun h => by simp [hxc] at h)
        simp only [Bool.or_eq_true, decide_eq_true_eq] at hc
        rcases hc with hc | hc
        · exact huD j hj hji hc
        · rw [noB _ (List.getElem_mem hj) hc] at hon; cases hon
      have hy : cntY (lOn l i T) < cntY l := by
        unfold cntY
        have h1 := C.cntOlder_eq (k1 := .B) (k2 := .D)
          ⟨fun j hj hji hc _ => huD j hj hji hc, fun h => (by rw [hxc] at h; cases h)⟩ (by simp [hxc])
        have h2 := C.cntOlder_lt (k1 := .A) (k2 := .A)
          ⟨fun j hj hji hc _ => huA j hj hji hc, fun _ => he⟩ hxc
          (fun s hs hc hon => (C.unb' hs hon
            (by simp [AuraSrc.negates_cat (C.simple s hs) (C.key_ne_on hs hon), hc, hxk])).2)
          hm hmi hac hao (huA m hm hmi hac)
        have h3 := C.cntOlder_eq (k1 := .D) (k2 := .B)
          ⟨fun j hj _ hc hon => (by rw [noB _ (List.getElem_mem hj) hc] at hon; cases hon),
           fun h => (by rw [hxc] at h; cases h)⟩ (by simp [hxc])
        omega
      exact .inr ⟨hr, .inr ⟨hx, .inl hy⟩⟩
    · -- 適用中になる
      have noA := noOn_of hA
      have he : effIn (lOn l i T) (l[i].turnOn T) = true := by
        rw [C.eff_x']
        rintro ⟨s, hs, hon, hn⟩
        rcases hneg s hs hon hn with hc | hc
        · have := noA s hs hc; rw [hon] at this; cases this
        · have := noD s hs hc; rw [hon] at this; cases this
      left
      have hr' : rankOf (lOn l i T) = 1 := by
        simp [rankOf, C.hasEff_lOn_false noD (fun h => by rw [hxc] at h; cases h), hasEff_lOn_of_x hxc he]
      rw [hr']
      unfold rankOf
      simp only [C.hasEff_false_of noD, C.hasEff_false_of noA, Bool.false_eq_true, ite_false]
      split <;> omega

end OnCtx
end turnOn

/-! ## 判定は必ず決まる -/

theorem measure_parts (L : List AuraSrc) :
    cntX L < 3 * L.length + 1 ∧ cntY L < 3 * L.length + 1 ∧ cntP L < 3 * L.length + 1 ∧
      cntOn L < 3 * L.length + 1 ∧ rankOf L ≤ 3 := by
  have hX := countP_range_lt_succ L.length
    (fun j => pAt L j fun s => (decide (s.cat = .D) || decide (s.cat = .B)) && !effIn L s)
  have hP := countP_range_lt_succ L.length (fun j => pAt L j fun s => decide (s.cat = .P) && !effIn L s)
  have hO := countP_range_lt_succ L.length (fun j => pAt L j (·.on))
  have h1 := countP_range_lt_succ L.length (fun j => pAt L j fun s => decide (s.cat = .B) && olderThan L s .D)
  have h2 := countP_range_lt_succ L.length (fun j => pAt L j fun s => decide (s.cat = .A) && olderThan L s .A)
  have h3 := countP_range_lt_succ L.length (fun j => pAt L j fun s => decide (s.cat = .D) && olderThan L s .B)
  refine ⟨by unfold cntX; omega, by unfold cntY cntOlder; omega, by unfold cntP; omega,
    by unfold cntOn; omega, ?_⟩
  unfold rankOf; split <;> (try split) <;> (try split) <;> omega

theorem settleMeasure_lt_fuel (L : List AuraSrc) : settleMeasure L < 4 * (3 * L.length + 1) ^ 4 := by
  obtain ⟨hX, hY, hP, hO, hr⟩ := measure_parts L
  have := enc_lt_bound (r := rankOf L) hX hY hP hO
  have h4 : (rankOf L + 1) * (3 * L.length + 1) * (3 * L.length + 1) * (3 * L.length + 1) * (3 * L.length + 1)
      ≤ 4 * (3 * L.length + 1) ^ 4 := by
    rw [Nat.pow_succ, Nat.pow_succ, Nat.pow_succ, Nat.pow_one]
    simp only [Nat.mul_assoc]
    exact Nat.mul_le_mul_right _ (by omega)
  unfold settleMeasure; omega

/-- **`settleOnce` で1回変えるたびに、量が減る** -/
theorem settleMeasure_lt {l l' : List AuraSrc} {c c' : Nat} (h : settleOnce l c = some (l', c'))
    (hS : ∀ s ∈ l, s.Simple) (hk : (l.map (·.key)).Nodup) : settleMeasure l' < settleMeasure l := by
  rcases settleOnce_some h with ⟨i, hi, hon, hb, rfl⟩ | ⟨hK, i, hi, hoff, hunb, rfl⟩
  · exact kill_measure hi hon hb
  · have C : OnCtx l i (newestTime l c) hi :=
      { simple := hS, nodup := hk, off := hoff, unb := hunb, kst := hK, newer := since_lt_newestTime }
    exact C.measure_lt

theorem settleOnce_preserve {l l' : List AuraSrc} {c c' : Nat} (h : settleOnce l c = some (l', c'))
    (hS : ∀ s ∈ l, s.Simple) (hk : (l.map (·.key)).Nodup) :
    (∀ s ∈ l', s.Simple) ∧ (l'.map (·.key)).Nodup ∧ l'.length = l.length := by
  have hm := settleOnce_keys h
  refine ⟨fun s hs => ?_, ?_, ?_⟩
  · have : (s.who, s.kind, s.key, s.auras) ∈ l.map (fun s => (s.who, s.kind, s.key, s.auras)) := by
      rw [← hm]; exact List.mem_map_of_mem hs
    obtain ⟨t, ht, he⟩ := List.mem_map.mp this
    simp only [Prod.mk.injEq] at he
    have := hS t ht
    unfold AuraSrc.Simple AuraSrc.nm AuraSrc.nt at this ⊢
    rw [← he.2.1, ← he.2.2.2]; exact this
  · have : l'.map (·.key) = l.map (·.key) := by
      have := congrArg (List.map (fun p : PlayerId × SrcKind × (Nat × Nat × Nat) × List Aura => p.2.2.1)) hm
      simpa [List.map_map, Function.comp_def] using this
    rw [this]; exact hk
  · have := congrArg List.length hm; simpa using this

theorem settleAux_settled (n : Nat) (l : List AuraSrc) (c : Nat) (hS : ∀ s ∈ l, s.Simple)
    (hk : (l.map (·.key)).Nodup) (hn : settleMeasure l < n) :
    settleOnce (settleAux n l c).1 (settleAux n l c).2 = none := by
  induction n generalizing l c with
  | zero => omega
  | succ n ih =>
    simp only [settleAux]
    split
    · rename_i l' c' h
      have hlt := settleMeasure_lt h hS hk
      obtain ⟨hS', hk', -⟩ := settleOnce_preserve h hS hk
      exact ih l' c' hS' hk' (by omega)
    · assumption

/-- **判定は必ず決まる**：カードが `AuraSrc.Simple` を満たし、識別が重ならなければ、`settle` の結果は
もう `settleOnce` で変わらない -/
theorem settle_settled (l : List AuraSrc) (c : Nat) (hS : ∀ s ∈ l, s.Simple) (hk : (l.map (·.key)).Nodup) :
    settleOnce (settle l c).1 (settle l c).2 = none :=
  settleAux_settled _ l c hS hk (settleMeasure_lt_fuel l)

/-! ## 盤面での判定 -/

theorem filterMap_sublist_map {α β : Type} {l : List α} {g : α → Option β} {h : α → β}
    (H : ∀ x, g x = none ∨ g x = some (h x)) : (l.filterMap g).Sublist (l.map h) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.filterMap_cons, List.map_cons]
    rcases H a with h1 | h1 <;> rw [h1]
    · exact ih.cons _
    · exact ih.cons_cons _

theorem nodup_map_of_inj {α β : Type} {l : List α} {f : α → β} (hl : l.Nodup)
    (hf : ∀ a b, f a = f b → a = b) : (l.map f).Nodup :=
  List.Pairwise.map f (fun a b h e => h (hf a b e)) hl

theorem Player.keys_sublist (p : Player) (w : PlayerId) :
    ((p.sources w).map (·.key)).Sublist
      ((List.range p.backrow.length).map (stKey w) ++ p.monsters.map (fun m => monKey m.uid)) := by
  unfold Player.sources
  rw [List.map_append, List.map_filterMap, List.map_filterMap]
  apply List.Sublist.append
  · apply filterMap_sublist_map
    intro x
    cases p.backrow[x]? with
    | none => simp
    | some s => cases s.faceUp <;> simp
  · apply filterMap_sublist_map
    intro m
    by_cases h : m.pos = .faceDownDefense <;> simp [h]

/-- 盤面の永続効果を持つカードの識別は重ならない -/
theorem Board.sources_keys_nodup (b : Board) (hu : b.UidOK) : (b.sources.map (·.key)).Nodup := by
  have hsub : (b.sources.map (·.key)).Sublist
      (((List.range b.p1.backrow.length).map (stKey .one) ++ b.p1.monsters.map (fun m => monKey m.uid)) ++
       ((List.range b.p2.backrow.length).map (stKey .two) ++ b.p2.monsters.map (fun m => monKey m.uid))) := by
    unfold Board.sources; rw [List.map_append]
    exact (Player.keys_sublist _ _).append (Player.keys_sublist _ _)
  apply hsub.nodup
  have hn := hu.1
  unfold Board.uids Board.uidsOf at hn
  simp only [Board.get] at hn
  rw [List.nodup_append] at hn
  obtain ⟨hn1, hn2, hd⟩ := hn
  have hm : ∀ (ms : List FieldMonster), (ms.map (·.uid)).Nodup → (ms.map (fun m => monKey m.uid)).Nodup := by
    intro ms h
    have := nodup_map_of_inj (f := monKey) h (fun a b e => by simpa [monKey] using e)
    simpa [List.map_map, Function.comp_def] using this
  have hst : ∀ w n, ((List.range n).map (stKey w)).Nodup := fun w n =>
    nodup_map_of_inj List.nodup_range (fun a b e => by simpa [stKey] using e)
  rw [List.nodup_append, List.nodup_append, List.nodup_append]
  refine ⟨⟨hst _ _, hm _ hn1, ?_⟩, ⟨hst _ _, hm _ hn2, ?_⟩, ?_⟩
  · intro a ha c hc; simp only [List.mem_map, List.mem_range] at ha hc
    obtain ⟨_, _, rfl⟩ := ha; obtain ⟨_, _, rfl⟩ := hc; simp [stKey, monKey]
  · intro a ha c hc; simp only [List.mem_map, List.mem_range] at ha hc
    obtain ⟨_, _, rfl⟩ := ha; obtain ⟨_, _, rfl⟩ := hc; simp [stKey, monKey]
  · intro a ha c hc
    simp only [List.mem_append, List.mem_map, List.mem_range] at ha hc
    rcases ha with ⟨_, _, rfl⟩ | ⟨m1, hm1, rfl⟩ <;> rcases hc with ⟨_, _, rfl⟩ | ⟨m2, hm2, rfl⟩
    · simp [stKey, PlayerId.code]
    · simp [stKey, monKey]
    · simp [stKey, monKey]
    · simp only [monKey, ne_eq, Prod.mk.injEq, true_and]
      exact hd _ (List.mem_map_of_mem hm1) _ (List.mem_map_of_mem hm2)

/-- **盤面の永続効果の判定は必ず決まる**（カードが `AuraSrc.Simple` を満たし、モンスターの uid が重ならないとき） -/
theorem Board.settled (b : Board) (hu : b.UidOK) (hS : ∀ s ∈ b.sources, s.Simple) :
    settleOnce (settle b.sources b.clock).1 (settle b.sources b.clock).2 = none :=
  settle_settled _ _ hS (b.sources_keys_nodup hu)

/-- 対戦の途中のどの盤面でも、判定は決まっている -/
theorem reachable_settled {g : Game} (hr : Reachable g) (hS : ∀ s ∈ g.board.sources, s.Simple) :
    settleOnce (settle g.board.sources g.board.clock).1 (settle g.board.sources g.board.clock).2 = none :=
  g.board.settled (reachable_uidOK hr) hS

/-- **対戦の途中のどの盤面でも、有効なカード同士は互いに無効にしない** -/
theorem reachable_consistent {g : Game} (hr : Reachable g) (hS : ∀ s ∈ g.board.sources, s.Simple)
    {s t : AuraSrc} (hs : s ∈ g.board.effective) (ht : t ∈ g.board.effective) : t.beats s = false := by
  unfold Board.effective effectiveSources at hs ht
  rw [List.mem_filter] at hs ht
  exact settled_consistent (reachable_settled hr hS) hs.1 ht.1 hs.2 ht.2

/-- **対戦の途中のどの盤面でも、無効なカードには、それを無効にする有効なカードがある** -/
theorem reachable_negated_has_reason {g : Game} (hr : Reachable g) (hS : ∀ s ∈ g.board.sources, s.Simple)
    {s : AuraSrc} (hs : s ∈ (settle g.board.sources g.board.clock).1) (hso : s.on = false) :
    ∃ t ∈ g.board.effective, t.beats s = true := by
  obtain ⟨t, ht, hto, hb⟩ := negated_has_reason (reachable_settled hr hS) hs hso
  refine ⟨t, ?_, hb⟩
  unfold Board.effective effectiveSources
  exact List.mem_filter.mpr ⟨ht, hto⟩

/-! ## 例 -/

-- 3すくみ（スキルドレイン・サイコ・ショッカー・王宮のお触れ）の盤面のカードは条件を満たす
example : ∀ s ∈ Demo.triStart.board.sources, s.Simple := by decide
example : ∀ s ∈ (Demo.triDecree.toOption.map (·.board.sources)).getD [], s.Simple := by decide

/-- 条件を満たさないカードの組み合わせでは、判定が決まらないことがある。
スキルドレイン・王宮のお触れ・「モンスターの効果を無効にするモンスター」・「罠とモンスターの効果を無効にするモンスター」
をすべて無効の状態から判定すると、有効・無効が8回ごとに同じ並びに戻り、回り続ける。 -/
def loopSrcs : List AuraSrc :=
  [{ who := .one, kind := .trap, key := (1, 1, 0), since := 1, on := false, auras := [.negateMonsterEffects] },
   { who := .two, kind := .trap, key := (1, 2, 0), since := 2, on := false, auras := [.negateTraps] },
   { who := .one, kind := .monster, key := (0, 0, 0), since := 3, on := false, auras := [.negateMonsterEffects] },
   { who := .two, kind := .monster, key := (0, 0, 1), since := 4, on := false,
     auras := [.negateTraps, .negateMonsterEffects] }]

example : ¬ ∀ s ∈ loopSrcs, s.Simple := by decide

example : (settleAux 9 loopSrcs 4).1.map (·.on) = (settleAux 1 loopSrcs 4).1.map (·.on) ∧
    (settleAux 1 loopSrcs 4).1.map (·.on) = [true, false, false, false] := by decide

-- 上限の回数まで繰り返しても決まらない
/-- info: true -/
#guard_msgs in
#eval (settleOnce (settle loopSrcs 4).1 (settle loopSrcs 4).2).isSome

end YGO

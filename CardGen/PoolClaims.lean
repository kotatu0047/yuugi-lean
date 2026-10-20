import CardGen.Pool

/-!
# カードの一覧によって決まる★

| 型 | 規則 |
|---|---|
| F. ライフの上限 | 一覧に「回復」の動きを持つカードがなければ、ライフは初期ライフを超えない（`Reachable.life_le`） |
| G. ライフの下限 | 戦闘できる種類がなく、一覧に「ダメージ」の動きを持つカードがなければ、ライフは初期ライフより減らない（`Reachable.life_ge`） |
| H. 攻撃力・守備力の上限 | 一覧に攻撃力（守備力）を上げる「ターンの終わりまでの変化」を持つカードがなければ、フィールドのカードの攻撃力（守備力）は
「カードに書いた値の最大 ＋ 1枚の永続の変化の最大 × 両プレイヤーのフィールド上のカードの最大数」以下（`Reachable.atk_le`・`Reachable.def_le`） |

H の考え方（守備力も同じなので、`atk : Bool` で選んでまとめて証明する。`Reachable.stat_le`）：攻撃力は「カードに書いた値 ＋ ターンの終わりまでの変化 ＋ フィールド上の表側のカードの永続の変化の合計」。
ターンの終わりまでの変化は、上げるカードがなければ 0 以下のまま（`Reachable.bonus_le`）。永続の変化は、フィールド上の
1枚ごとに、そのカードの攻撃力の変化のうち正のものの合計を超えない。
-/

namespace CardGen

/-! ## ターンの終わりまでの変化は 0 以下

攻撃力と守備力は同じ形なので、`atk : Bool`（`true` なら攻撃力、`false` なら守備力）で選んでまとめて扱う。 -/

/-- 攻撃力（`atk = true`）か守備力（`false`）のほうのターンの終わりまでの変化 -/
def Slot.bonus (atk : Bool) (sl : Slot) : Int := bif atk then sl.atkBonus else sl.defBonus

/-- 攻撃力か守備力を変える永続の効果 -/
def Effect.mod (atk : Bool) : Effect → Option (Selector × Int) := bif atk then Effect.atkMod else Effect.defMod

/-- カードに書いた攻撃力か守備力 -/
def Card.stat (atk : Bool) (c : Card) : Nat := bif atk then c.attack else c.defense


/-- 攻撃力（守備力）を上げる「ターンの終わりまでの変化」 -/
def Action.raises (atk : Bool) : Action → Bool
  | .pump _ a d => decide (0 < bif atk then a else d)
  | _ => false

/-- 攻撃力（守備力）を上げる「ターンの終わりまでの変化」の動きを持つ -/
def Card.raises (atk : Bool) (c : Card) : Bool := c.effects.any fun
  | .activated as => as.any (Action.raises atk)
  | .triggered _ _ as => as.any (Action.raises atk)
  | _ => false

/-- 1人分のフィールドのどのカードも、ターンの終わりまでの攻撃力（守備力）の変化が 0 以下 -/
def PBonus (atk : Bool) (s : PState) : Prop := ∀ sl ∈ s.field, sl.bonus atk ≤ 0

/-- どちらのプレイヤーも `PBonus` -/
def BonusLe (atk : Bool) (g : State) : Prop := ∀ q, PBonus atk (g q)

section
variable {atk : Bool}

theorem PBonus.sub {s s' : PState} (h : PBonus atk s) (hs : ∀ sl ∈ s'.field, sl ∈ s.field) : PBonus atk s' :=
  fun sl hsl => h sl (hs sl hsl)

theorem BonusLe.set {g : State} {p : PlayerId} {s : PState} (h : BonusLe atk g) (hs : PBonus atk s) : BonusLe atk (g.set p s) := by
  intro q
  by_cases hq : q = p
  · subst hq; rw [State.set_same]; exact hs
  · rw [State.set_other _ _ hq]; exact h q

theorem BonusLe.map {g : State} {f : PlayerId → PState → PState} (hf : ∀ q, PBonus atk (f q (g q))) :
    BonusLe atk (g.map f) := by
  intro q; rw [State.map_apply]; exact hf q

theorem pbonus_mark {s : PState} (h : PBonus atk s) (d : Nat → Nat) : PBonus atk (s.mark d) := by
  intro sl hsl
  obtain ⟨i, hi, rfl⟩ := List.mem_mapIdx.1 hsl
  exact h s.field[i] (List.getElem_mem hi)

theorem pbonus_pump {s : PState} (h : PBonus atk s) (d : Nat → Int × Int)
    (hd : ∀ i, (bif atk then (d i).1 else (d i).2) ≤ 0) : PBonus atk (s.pump d) := by
  intro sl hsl
  obtain ⟨i, hi, rfl⟩ := List.mem_mapIdx.1 hsl
  have h1 := h _ (List.getElem_mem hi)
  have h2 := hd i
  cases atk
  · show s.field[i].defBonus + (d i).2 ≤ 0
    exact Int.add_nonpos h1 h2
  · show s.field[i].atkBonus + (d i).1 ≤ 0
    exact Int.add_nonpos h1 h2

theorem pbonus_sweep {s : PState} (h : PBonus atk s) (dead : Nat → Slot → Bool) : PBonus atk (s.sweep dead) := by
  refine h.sub fun sl hsl => ?_
  simp only [PState.sweep, List.mem_map, List.mem_filter] at hsl
  obtain ⟨y, ⟨hy, _⟩, rfl⟩ := hsl
  have := List.mem_map_of_mem (f := Prod.fst) hy
  rwa [List.zipIdx_map_fst] at this

theorem pbonus_destroyAt {s : PState} (h : PBonus atk s) (k : Nat) : PBonus atk (s.destroyAt k) := by
  unfold PState.destroyAt
  split
  · exact h.sub fun sl hsl => (List.eraseIdx_sublist _ _).subset hsl
  · exact h

theorem bonusLe_sweep (r : Rules) {g : State} (h : BonusLe atk g) (neg : List Pos) : BonusLe atk (g.sweep r neg) :=
  BonusLe.map fun q => pbonus_sweep (h q) _

theorem bonusLe_applyAction (r : Rules) (src : Src) (negS : List (PlayerId × Slot)) {g : State}
    (h : BonusLe atk g) (a : Action) (ha : a.raises atk = false) : BonusLe atk (g.applyAction r src negS a) := by
  cases a with
  | destroy sel => exact BonusLe.map fun q => (h q).sub fun sl hsl => (List.mem_filter.1 hsl).1
  | bounce sel => exact BonusLe.map fun q => (h q).sub fun sl hsl => (List.mem_filter.1 hsl).1
  | counter sel => exact BonusLe.map fun q => (h q).sub fun sl hsl => (List.mem_filter.1 hsl).1
  | draw n => exact h.set (h src.p)
  | damage n => exact h.set (h (!src.p))
  | heal n => exact h.set (h src.p)
  | strike sel n =>
    have h1 : BonusLe atk (g.strikeMarks r sel n src) := BonusLe.map fun q => pbonus_mark (h q) _
    exact bonusLe_sweep r h1 _
  | pump sel a d =>
    have ha' : (bif atk then a else d) ≤ 0 := by simp only [Action.raises, decide_eq_false_iff_not] at ha; omega
    have h1 : BonusLe atk (g.pumpMarks r sel a d src) := BonusLe.map fun q => pbonus_pump (h q) _ fun i => by
      split
      · split
        · exact ha'
        · cases atk <;> exact Int.le_refl 0
      · cases atk <;> exact Int.le_refl 0
    exact bonusLe_sweep r h1 _

theorem bonusLe_foldl (r : Rules) (p : Src) (negS : List (PlayerId × Slot)) (as : List Action)
    (has : as.any (Action.raises atk) = false) :
    ∀ {g : State}, BonusLe atk g → BonusLe atk (as.foldl (State.applyAction r p negS) g) := by
  induction as with
  | nil => exact fun h => h
  | cons a t ih =>
    intro g h
    simp only [List.any_cons, Bool.or_eq_false_iff] at has
    exact ih has.2 (bonusLe_applyAction r p negS h a has.1)

theorem bonusLe_duel (r : Rules) {g : State} (h : BonusLe atk g) (neg : List Pos) (p : PlayerId) (k : Nat) (sl : Slot)
    (t : Option Nat) : BonusLe atk (g.duel r neg p k sl t) := by
  have dd : ∀ (j n : Nat) (s : PState), PBonus atk s → PBonus atk ((s.destroyAt j).damage n) :=
    fun j n s hs => pbonus_destroyAt hs j
  cases t with
  | none => exact h.set (h _)
  | some j =>
    simp only [State.duel]
    split
    · exact h
    · split
      · split
        · exact h.set (dd _ _ _ (h _))
        · split
          · exact h.set (dd _ _ _ (h _))
          · split
            · exact h
            · have hne : (!p) ≠ p := by cases p <;> decide
              refine (h.set (pbonus_destroyAt (h p) k)).set ?_
              exact pbonus_destroyAt (h _) _
      · split
        · exact h.set (pbonus_destroyAt (h _) _)
        · split
          · exact h.set (h _)
          · exact h

theorem bonusLe_combat (r : Rules) {g : State} (h : BonusLe atk g) (neg : List Pos) (p : PlayerId) (atks : List Nat)
    (blocks : List (Nat × Nat)) : BonusLe atk (g.combat r neg p atks blocks) := by
  simp only [State.combat]
  refine bonusLe_sweep r ?_ neg
  exact (h.set (pbonus_mark (h p) _)).set (pbonus_mark (h _) _)

/-- 一覧のカード `c` が攻撃力（守備力）を上げる変化を持たなければ、その効果の動き `as` にもない -/
theorem noRaise_of_pool {pool : List Card} (hr : pool.all (!·.raises atk) = true) {c : Card} (hc : c ∈ pool)
    {as : List Action} (h : .activated as ∈ c.effects ∨ ∃ on opt, .triggered on opt as ∈ c.effects) :
    as.any (Action.raises atk) = false := by
  have hno : c.raises atk = false := by
    have := List.all_eq_true.1 hr _ hc
    simpa using this
  unfold Card.raises at hno
  rcases h with h | ⟨on, opt, h⟩
  · have := List.any_eq_false.1 hno _ h
    simpa using this
  · have := List.any_eq_false.1 hno _ h
    simpa using this

/-- **一覧に攻撃力（守備力）を上げる「ターンの終わりまでの変化」を持つカードがなければ、
到達できるどの状態でも、フィールドのカードのターンの終わりまでの攻撃力（守備力）の変化は 0 以下** -/
theorem Reachable.bonus_le {r : Rules} {decks : PlayerId → List Card} {pool : List Card}
    (hpool : ∀ p, ∀ x ∈ decks p, x ∈ pool) (hr : pool.all (!·.raises atk) = true)
    {g : State} (hg : Reachable r decks g) : BonusLe atk g := by
  induction hg with
  | start => intro q sl hsl; simp [CardGen.start] at hsl
  | @step g g' hg' hs ih =>
    cases hs with
    | draw p c d hd => exact ih.set (ih p)
    | place p c i z up _ _ _ _ _ =>
      refine ih.set fun sl hsl => ?_
      rcases List.mem_append.1 hsl with h | h
      · exact ih p sl h
      · simp only [List.mem_singleton] at h; subst h; cases atk <;> exact Int.le_refl 0
    | attack p k sl t neg _ _ _ _ =>
      unfold State.battle
      split
      · exact bonusLe_combat r ih neg p _ _
      · exact bonusLe_duel r ih neg p k sl t
    | combat p atk blocks neg _ => exact bonusLe_combat r ih neg p atk blocks
    | mend =>
      refine BonusLe.map fun q sl hsl => ?_
      obtain ⟨sl0, -, rfl⟩ := List.mem_map.1 hsl
      cases atk <;> exact Int.le_refl 0
    | discard p c _ => exact ih.set (ih p)
    | settle neg => exact bonusLe_sweep r ih neg
    | resolve p k sl as apply neg tgt hk hact =>
      have hcard : sl.card ∈ pool := (hg'.fromPool hpool).field (List.mem_of_getElem? hk)
      have has := noRaise_of_pool hr hcard (.inl hact)
      let g1 := g.set p { g p with field := (g p).field.eraseIdx k }
      have h1 : BonusLe atk g1 := ih.set ((ih p).sub fun sl hsl => (List.eraseIdx_sublist _ _).subset hsl)
      have h2 : BonusLe atk
          (if apply then as.foldl (State.applyAction r (g.srcOf r p sl tgt) (g.negSlots neg)) g1 else g1) := by
        split
        · exact bonusLe_foldl r _ _ as has h1
        · exact h1
      exact h2.set (h2 p)
    | trigger p c on opt as cell apply neg tgt hact hc =>
      have hcard : c ∈ pool := hg'.fromPool hpool p c (PState.mem_cards.2 hc)
      have has := noRaise_of_pool hr hcard (.inr ⟨on, opt, hact⟩)
      unfold State.fire
      split
      · exact bonusLe_foldl r _ _ as has ih
      · exact ih

end

/-! ## 永続の攻撃力（守備力）の変化 -/

/-- カード `c` の永続の攻撃力（守備力）の変化のうち、正のものの合計（1枚が、あるカードの値を上げうる量の上限） -/
def Card.boostSum (atk : Bool) (c : Card) : Int :=
  (c.effects.map fun e => match e.mod atk with
    | some (_, n) => max n 0
    | none => 0).sum

theorem sum_map_le_int {α} (l : List α) (f g : α → Int) (h : ∀ x ∈ l, f x ≤ g x) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons]
    have h1 := h a List.mem_cons_self
    have h2 := ih fun x hx => h x (List.mem_cons_of_mem _ hx)
    omega

theorem Card.boostSum_nonneg (atk : Bool) (c : Card) : 0 ≤ c.boostSum atk := by
  unfold Card.boostSum
  generalize c.effects = l
  induction l with
  | nil => simp
  | cons e t ih =>
    simp only [List.map_cons, List.sum_cons]
    split
    · exact Int.add_nonneg (Int.le_max_right _ _) ih
    · omega

/-- 1枚の永続の効果で変わる攻撃力（守備力）は、そのカードが「フィールド上」にあれば `boostSum` 以下、なければ 0 以下 -/
theorem modFrom_le (atk : Bool) (r : Rules) (neg : List Pos) (t : Pos) (tsl : Slot) (q : PlayerId) (j : Nat)
    (src : Slot) :
    modFrom r (Effect.mod atk) neg t tsl q j src ≤ if r.onFieldZone src.zone then src.card.boostSum atk else 0 := by
  unfold modFrom
  split
  · rename_i hc
    simp only [Bool.and_eq_true] at hc
    simp only [hc.1.2, ↓reduceIte]
    apply sum_map_le_int
    intro e _
    cases e.mod atk with
    | none => exact Int.le_refl 0
    | some p =>
      obtain ⟨sel, n⟩ := p
      show (if _ then n else 0) ≤ max n 0
      split
      · exact Int.le_max_left _ _
      · exact Int.le_max_right _ _
  · split
    · exact src.card.boostSum_nonneg atk
    · exact Int.le_refl 0

/-- 番号ごとの値 `F j` が、どれも `j` 番目の要素の上限 `g l[j]` 以下なら、その合計も上限の合計以下 -/
theorem sum_range_le {α} (l : List α) (F : Nat → Int) (g : α → Int)
    (h : ∀ j (hj : j < l.length), F j ≤ g l[j]) :
    ((List.range l.length).map F).sum ≤ (l.map g).sum := by
  induction l generalizing F with
  | nil => simp
  | cons a t ih =>
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map, List.sum_cons, List.map_cons,
      List.sum_cons]
    have h1 : F 0 ≤ g a := h 0 (by simp)
    have h2 := ih (fun j => F (j + 1)) fun j hj => h (j + 1) (by simp; omega)
    simp only [Function.comp_def, Nat.succ_eq_add_one] at h2 ⊢
    omega

/-- 条件に合うものだけ `B`、ほかは 0 として足すと、`B` × 合う個数 -/
theorem sum_ite_eq {α} (l : List α) (p : α → Bool) (B : Int) :
    (l.map fun x => if p x then B else 0).sum = B * (l.filter p).length := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons, List.filter_cons, ih]
    split <;> simp [Int.mul_add] <;> omega

/-! ## 攻撃力（守備力）の上限 -/

/-- 一覧のカードに書いた攻撃力（守備力）の最大 -/
def maxStat (atk : Bool) (pool : List Card) : Nat := (pool.map (·.stat atk)).foldr max 0

/-- 一覧のカード1枚の、永続の攻撃力（守備力）の変化の合計の最大 -/
def poolBoost (atk : Bool) (pool : List Card) : Nat := (pool.map (·.boostSum atk |>.toNat)).foldr max 0

/-- 1人分のフィールド上のカードの最大数（「何枚でも」のゾーンがあれば、デッキの枚数） -/
def fieldCap (r : Rules) : Nat := if r.bounded none then r.bound none else r.deckSize

theorem le_foldr_max {l : List Nat} {x : Nat} (h : x ∈ l) : x ≤ l.foldr max 0 := by
  induction l with
  | nil => cases h
  | cons a t ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.1 h with rfl | h
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih h) (Nat.le_max_right _ _)

theorem Inv.onField_le {r : Rules} {g : State} (h : Inv r g) (p : PlayerId) :
    ((g p).field.filter fun sl => r.onFieldZone sl.zone).length ≤ fieldCap r := by
  have e : ((g p).field.filter fun sl => r.onFieldZone sl.zone).length = fieldCount r none (g p) := by
    simp [fieldCount]
  unfold fieldCap
  split
  · rename_i hb
    rw [e]; exact fieldCount_le_bound h p hb
  · have h1 := List.length_filter_le (fun sl : Slot => r.onFieldZone sl.zone) (g p).field
    have h2 := h.size p
    simp only [PState.size] at h2
    omega

/-- `q` のフィールド全体からの永続の攻撃力（守備力）の変化は、`poolBoost` × フィールド上のカードの最大数 以下 -/
theorem modSide_le (atk : Bool) {r : Rules} {g : State} {pool : List Card} (hinv : Inv r g) (hfrom : FromPool pool g)
    (neg : List Pos) (t : Pos) (tsl : Slot) (q : PlayerId) :
    g.modSide r (Effect.mod atk) neg t tsl q ≤ (poolBoost atk pool : Int) * (fieldCap r : Int) := by
  have hB : ∀ sl ∈ (g q).field, sl.card.boostSum atk ≤ (poolBoost atk pool : Int) := by
    intro sl hsl
    have hc := hfrom.field hsl
    have := le_foldr_max (List.mem_map_of_mem (f := fun c : Card => (c.boostSum atk).toNat) hc)
    have := sl.card.boostSum_nonneg atk
    unfold poolBoost
    omega
  have h1 := sum_range_le (g q).field (fun j => match (g q).field[j]? with
      | some src => modFrom r (Effect.mod atk) neg t tsl q j src
      | none => 0)
    (fun src => if r.onFieldZone src.zone then (poolBoost atk pool : Int) else 0) (by
      intro j hj
      show (match (g q).field[j]? with
        | some src => modFrom r (Effect.mod atk) neg t tsl q j src
        | none => 0) ≤ _
      rw [List.getElem?_eq_getElem hj]
      refine Int.le_trans (modFrom_le atk r neg t tsl q j _) ?_
      split
      · exact hB _ (List.getElem_mem hj)
      · exact Int.le_refl 0)
  rw [sum_ite_eq] at h1
  have h2 := hinv.onField_le q
  have h3 : (poolBoost atk pool : Int) * (((g q).field.filter fun sl => r.onFieldZone sl.zone).length : Int) ≤
      (poolBoost atk pool : Int) * (fieldCap r : Int) :=
    Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
  exact Int.le_trans h1 h3

/-- 攻撃力（守備力）の値の上限 -/
def statCap (atk : Bool) (r : Rules) (pool : List Card) : Nat :=
  maxStat atk pool + 2 * (poolBoost atk pool * fieldCap r)

/-- 攻撃力（守備力）：カードに書いた値 ＋ ターンの終わりまでの変化 ＋ 両プレイヤーのフィールドからの永続の変化 -/
theorem State.statOf_eq (atk : Bool) (r : Rules) (g : State) (neg : List Pos) (t : Pos) (tsl : Slot) :
    (bif atk then g.atkOf r neg t tsl else g.defOf r neg t tsl) =
      (Int.ofNat (tsl.card.stat atk) + tsl.bonus atk + g.modSide r (Effect.mod atk) neg t tsl true +
        g.modSide r (Effect.mod atk) neg t tsl false).toNat := by
  cases atk <;> rfl

/-- **一覧に攻撃力（守備力）を上げる「ターンの終わりまでの変化」を持つカードがなければ、到達できるどの状態でも、
フィールドのどのカードの攻撃力（守備力）も「カードに書いた値の最大 ＋ 2 ×（1枚の永続の変化の最大 × 1人分のフィールド上の
カードの最大数）」以下** -/
theorem Reachable.stat_le (atk : Bool) {r : Rules} {decks : PlayerId → List Card} {pool : List Card}
    (hpool : ∀ p, ∀ x ∈ decks p, x ∈ pool) (hr : pool.all (!·.raises atk) = true)
    (hd : ∀ p, (decks p).length = r.deckSize) {g : State} (hg : Reachable r decks g)
    (p : PlayerId) (k : Nat) (sl : Slot) (neg : List Pos) (hk : (g p).field[k]? = some sl) :
    (bif atk then g.atkOf r neg (p, k) sl else g.defOf r neg (p, k) sl) ≤ statCap atk r pool := by
  have hfrom := hg.fromPool hpool
  have hinv := hg.inv hd
  have hsl := List.mem_of_getElem? hk
  have ha : sl.card.stat atk ≤ maxStat atk pool := le_foldr_max (List.mem_map_of_mem (hfrom.field hsl))
  have hb : sl.bonus atk ≤ 0 := hg.bonus_le hpool hr p sl hsl
  have m1 := modSide_le atk hinv hfrom neg (p, k) sl true
  have m2 := modSide_le atk hinv hfrom neg (p, k) sl false
  rw [State.statOf_eq]
  unfold statCap
  apply Int.toNat_le.2
  simp only [Int.ofNat_eq_natCast, Int.natCast_add, Int.natCast_mul]
  omega

/-- **攻撃力の上限**（★の型 H） -/
theorem Reachable.atk_le {r : Rules} {decks : PlayerId → List Card} {pool : List Card}
    (hpool : ∀ p, ∀ x ∈ decks p, x ∈ pool) (hr : pool.all (!·.raises true) = true)
    (hd : ∀ p, (decks p).length = r.deckSize) {g : State} (hg : Reachable r decks g)
    (p : PlayerId) (k : Nat) (sl : Slot) (neg : List Pos) (hk : (g p).field[k]? = some sl) :
    g.atkOf r neg (p, k) sl ≤ statCap true r pool :=
  hg.stat_le true hpool hr hd p k sl neg hk

/-- **守備力の上限**（★の型 H） -/
theorem Reachable.def_le {r : Rules} {decks : PlayerId → List Card} {pool : List Card}
    (hpool : ∀ p, ∀ x ∈ decks p, x ∈ pool) (hr : pool.all (!·.raises false) = true)
    (hd : ∀ p, (decks p).length = r.deckSize) {g : State} (hg : Reachable r decks g)
    (p : PlayerId) (k : Nat) (sl : Slot) (neg : List Pos) (hk : (g p).field[k]? = some sl) :
    g.defOf r neg (p, k) sl ≤ statCap false r pool :=
  hg.stat_le false hpool hr hd p k sl neg hk

/-! ## カードの一覧によって決まる★の列挙 -/

/-- カードの一覧によって決まる★の中身 -/
def gameProps (g : Game) : List ClaimProp :=
  (if g.rules.life > 0 && g.cards.all (!·.heals) then [.lifeMax g.rules.life] else []) ++
  (if g.rules.life > 0 && g.rules.fighters.isEmpty && g.cards.all (!·.damages) then [.lifeMin g.rules.life] else []) ++
  (if !g.rules.fighters.isEmpty && g.cards.all (!·.raises true) then
    [.atkMax (maxStat true g.cards) (poolBoost true g.cards) (fieldCap g.rules)] else []) ++
  (if !g.rules.fighters.isEmpty && g.cards.all (!·.raises false) then
    [.defMax (maxStat false g.cards) (poolBoost false g.cards) (fieldCap g.rules)] else [])

/-- **カードの一覧によって決まる★は、一覧のカードで作ったどのデッキでも成り立つ**（デッキの枚数がルールどおりなら） -/
theorem gameProps_sound (g : Game) (decks : PlayerId → List Card) (hpool : ∀ p, ∀ x ∈ decks p, x ∈ g.cards)
    (hd : ∀ p, (decks p).length = g.rules.deckSize) :
    ∀ c ∈ gameProps g, c.Valid g.rules decks := by
  intro c hc
  unfold gameProps at hc
  simp only [List.mem_append] at hc
  rcases hc with ((hc | hc) | hc) | hc
  · split at hc
    · rename_i h
      simp only [List.mem_singleton] at hc; subst hc
      simp only [Bool.and_eq_true] at h
      simp only [ClaimProp.Valid, ClaimProp.atStart]
      intro s hs p
      exact hs.life_le hpool h.2 p
    · simp at hc
  · split at hc
    · rename_i h
      simp only [List.mem_singleton] at hc; subst hc
      simp only [Bool.and_eq_true, List.isEmpty_iff] at h
      simp only [ClaimProp.Valid, ClaimProp.atStart]
      intro s hs p
      exact hs.life_ge hpool h.2 h.1.2 p
    · simp at hc
  · split at hc
    · rename_i h
      simp only [List.mem_singleton] at hc; subst hc
      simp only [Bool.and_eq_true] at h
      simp only [ClaimProp.Valid, ClaimProp.atStart]
      intro s hs p k sl neg hk
      exact hs.atk_le hpool h.2 hd p k sl neg hk
    · simp at hc
  · split at hc
    · rename_i h
      simp only [List.mem_singleton] at hc; subst hc
      simp only [Bool.and_eq_true] at h
      simp only [ClaimProp.Valid, ClaimProp.atStart]
      intro s hs p k sl neg hk
      exact hs.def_le hpool h.2 hd p k sl neg hk
    · simp at hc

/-- 人が読む形の、カードの一覧によって決まる★ -/
def gameClaims (g : Game) : List Claim := (gameProps g).map (·.describe g.rules)

theorem gameClaims_valid (g : Game) (decks : PlayerId → List Card) (hpool : ∀ p, ∀ x ∈ decks p, x ∈ g.cards)
    (hd : ∀ p, (decks p).length = g.rules.deckSize) :
    ∀ c ∈ gameClaims g, c.prop.Valid g.rules decks := by
  intro c hc
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hc
  rw [ClaimProp.describe_prop]
  exact gameProps_sound g decks hpool hd p hp

end CardGen

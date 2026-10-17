import YuugiLean.Settle

/-!
# デッキのカードから、判定が必ず止まる条件を導く

`Settle.lean` の「判定は必ず止まる」（`reachable_settled`）は、盤面のカードが条件（`AuraSrc.Simple`）を
満たすことを仮定している。ここでは、その条件をカードの性質（`Card.simple`）として書き、

* カードはどこへ動いても `Card.simple` のまま（`step_good`）
* フィールドのカードが `Card.simple` なら、盤面のカードは `AuraSrc.Simple` を満たす（`Board.Good.sources_simple`）

を示す。これにより、**デッキとエクストラデッキのカードがすべて条件を満たせば、対戦の途中のどの盤面でも
判定は必ず止まる**（`simpleReachable_settled`）。D－HERO Bloo－D 以外の今あるカードは条件を満たす。
-/

namespace YGO

/-! ## カードの条件 -/

/-- 永続効果の組が、判定が必ず止まる条件を満たすか（`AuraSrc.Simple` と同じ内容） -/
def auraSimple (k : SrcKind) (as : List Aura) : Bool :=
  (!as.contains .negateMonsterEffects || (k == .trap && !as.contains .negateTraps)) &&
  (!as.contains .negateTraps || k != .spell) &&
  !as.contains .negateOppMonsterEffects

theorem AuraSrc.simple_iff (s : AuraSrc) : s.Simple ↔ auraSimple s.kind s.auras = true := by
  unfold AuraSrc.Simple AuraSrc.nm AuraSrc.nt AuraSrc.nmo auraSimple
  cases s.kind <;> cases s.auras.contains .negateMonsterEffects <;> cases s.auras.contains .negateTraps <;>
    cases s.auras.contains .negateOppMonsterEffects <;> simp

/-- 魔法・罠ゾーンに表側表示で置かれたときの条件 -/
def Card.stSimple (c : Card) : Bool := auraSimple (if c.isTrap then .trap else .spell) c.auras

/-- モンスターとしてフィールドに出たときの条件 -/
def MonsterCard.simple (m : MonsterCard) : Bool := auraSimple .monster (m.effects.filterMap MonsterEffect.aura?)

/-- **カードの条件**：フィールドに出たときに、判定が必ず止まる条件（`AuraSrc.Simple`）を満たす。
正規の方法で特殊召喚されたかの印（`MonsterCard.proper`）にはよらない。 -/
def Card.simple : Card → Bool
  | .monster m => m.simple
  | c => c.stSimple

@[simp] theorem Card.simple_proper (m : MonsterCard) (b : Bool) :
    (Card.monster { m with proper := b }).simple = (Card.monster m).simple := rfl

theorem Card.stSimple_of {c : Card} (h : c.simple = true) : c.stSimple = true := by
  cases c with
  | monster m => rfl
  | spell => exact h
  | trap => exact h

/-! ## 不変条件：どのカードも条件を満たす -/

def Player.Good (p : Player) : Prop :=
  (∀ c ∈ p.deck, c.simple = true) ∧ (∀ c ∈ p.extra, c.simple = true) ∧ (∀ c ∈ p.hand, c.simple = true) ∧
  (∀ s ∈ p.backrow, s.card.simple = true) ∧ (∀ c ∈ p.grave, c.simple = true) ∧
  (∀ m ∈ p.monsters, m.card.simple = true ∧ ∀ c ∈ m.overlays, c.simple = true)

def Board.Good (b : Board) : Prop := b.p1.Good ∧ b.p2.Good

/-- チェーン上の魔法・罠カード（モンスター効果のブロックはカードを動かさないので含めない） -/
def ChainGood (ch : List ChainLink) : Prop := ∀ l ∈ ch, l.mon = false → l.card.simple = true

def ChainState.Good (s : ChainState) : Prop := s.board.Good ∧ ChainGood s.chain

def Game.Good (g : Game) : Prop := g.board.Good ∧ ChainGood g.chain

/-! ### リストの補題 -/

theorem mem_removeIdxs_go {α : Type} (is : List Nat) :
    ∀ (i : Nat) (l : List α) {x : α}, x ∈ (removeIdxs.go is i l).1 ∨ x ∈ (removeIdxs.go is i l).2 → x ∈ l := by
  intro i l
  induction l generalizing i with
  | nil => simp [removeIdxs.go]
  | cons a l ih =>
    intro x hx
    simp only [removeIdxs.go] at hx
    split at hx
    · rcases hx with hx | hx
      · exact List.mem_cons_of_mem _ (ih _ (.inl hx))
      · rcases List.mem_cons.mp hx with rfl | hx
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (ih _ (.inr hx))
    · rcases hx with hx | hx
      · rcases List.mem_cons.mp hx with rfl | hx
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (ih _ (.inl hx))
      · exact List.mem_cons_of_mem _ (ih _ (.inr hx))

theorem mem_removeIdxs_1 {α : Type} {l : List α} {is : List Nat} {x : α} (h : x ∈ (removeIdxs l is).1) : x ∈ l :=
  mem_removeIdxs_go is 0 l (.inl h)

theorem mem_removeIdxs_2 {α : Type} {l : List α} {is : List Nat} {x : α} (h : x ∈ (removeIdxs l is).2) : x ∈ l :=
  mem_removeIdxs_go is 0 l (.inr h)

/-! ### 盤面の補題 -/

namespace Board.Good

theorem get {b : Board} (h : b.Good) (v : PlayerId) : (b.get v).Good := by
  cases v
  · exact h.1
  · exact h.2

theorem set {b : Board} (h : b.Good) (w : PlayerId) {p : Player} (hp : p.Good) : (b.set w p).Good := by
  cases w
  · exact ⟨hp, h.2⟩
  · exact ⟨h.1, hp⟩

theorem modify {b : Board} (h : b.Good) (w : PlayerId) {f : Player → Player} (hf : (f (b.get w)).Good) :
    (b.modify w f).Good := h.set w hf

theorem modifyP {b : Board} (h : b.Good) (w : PlayerId) {f : Player → Player}
    (hf : ∀ p : Player, p.Good → (f p).Good) : (b.modify w f).Good := h.modify w (hf _ (h.get w))

theorem withLog {b : Board} (h : b.Good) (l : List Happened) : ({ b with log := l } : Board).Good := h
theorem withClock {b : Board} (h : b.Good) (n : Nat) : ({ b with clock := n } : Board).Good := h

theorem iteLog {p : Prop} [Decidable p] {x : Board} {l : List Happened} (h : x.Good) :
    (if p then { x with log := l } else x).Good := by split <;> exact h
theorem iteClock {p : Prop} [Decidable p] {x : Board} {n : Nat} (h : x.Good) :
    (if p then { x with clock := n } else x).Good := by split <;> exact h

theorem with_ {b : Board} (h : b.Good) (b' : Board) (h1 : b'.p1 = b.p1) (h2 : b'.p2 = b.p2) : b'.Good := by
  unfold Board.Good; rw [h1, h2]; exact h

end Board.Good

/-- フィールドのモンスターの中身（カードと X 素材）を変えない変更 -/
theorem Player.Good.mapMon {p : Player} (h : p.Good) (f : FieldMonster → FieldMonster)
    (hf : ∀ m, (f m).card.simple = m.card.simple ∧ (f m).overlays = m.overlays) :
    ({ p with monsters := p.monsters.map f } : Player).Good := by
  refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, fun m hm => ?_⟩
  obtain ⟨m0, hm0, rfl⟩ := List.mem_map.mp hm
  rw [(hf m0).1, (hf m0).2]
  exact h.2.2.2.2.2 m0 hm0

theorem Board.Good.updMon {b : Board} (h : b.Good) (w : PlayerId) (u : Nat) (f : FieldMonster → FieldMonster)
    (hf : ∀ m, (f m).card = m.card ∧ (f m).overlays = m.overlays) : (b.updMon w u f).Good := by
  unfold Board.updMon
  refine h.modify w ((h.get w).mapMon _ fun m => ?_)
  split
  · rw [(hf m).1, (hf m).2]; exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩

theorem Board.Good.place {b : Board} (h : b.Good) (w : PlayerId) {c : MonsterCard} (hc : (Card.monster c).simple)
    (pos : Position) (t : Nat) (emz : Bool) (ev : Option Event) {ov : List Card} (hov : ∀ x ∈ ov, x.simple = true) :
    (b.place w c pos t emz ev ov).Good := by
  unfold Board.place
  refine Board.Good.with_ (h.modify w ?_) _ rfl rfl
  have hp := h.get w
  refine ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2.1, fun m hm => ?_⟩
  rcases List.mem_append.mp hm with hm | hm
  · exact hp.2.2.2.2.2 m hm
  · simp only [List.mem_singleton] at hm; subst hm; exact ⟨hc, hov⟩

theorem Board.Good.setMonAt {b : Board} (h : b.Good) (w : PlayerId) (i : Nat) {m : FieldMonster}
    (hm : m.card.simple = true ∧ ∀ c ∈ m.overlays, c.simple = true) : (b.setMonAt w i m).Good := by
  unfold Board.setMonAt
  have hp := h.get w
  refine h.modify w ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2.1, fun x hx => ?_⟩
  rcases List.mem_or_eq_of_mem_set hx with hx | rfl
  · exact hp.2.2.2.2.2 x hx
  · exact hm

/-! ### 墓地へ送る・破壊する -/

theorem Player.Good.dropEquips {p : Player} (h : p.Good) (u : Nat) :
    ({ p with backrow := p.backrow.filter (·.equipTo != some u)
              grave := p.grave ++ (p.backrow.filter (·.equipTo == some u)).map (·.card) } : Player).Good := by
  refine ⟨h.1, h.2.1, h.2.2.1, fun s hs => h.2.2.2.1 s (List.mem_filter.mp hs).1, fun c hc => ?_, h.2.2.2.2.2⟩
  rcases List.mem_append.mp hc with hc | hc
  · exact h.2.2.2.2.1 c hc
  · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hc
    exact h.2.2.2.1 s (List.mem_filter.mp hs).1

theorem Player.Good.removeBackrow {p : Player} (h : p.Good) (is : List Nat) :
    ({ p with backrow := (removeIdxs p.backrow is).1
              grave := p.grave ++ (removeIdxs p.backrow is).2.map (·.card) } : Player).Good := by
  refine ⟨h.1, h.2.1, h.2.2.1, fun s hs => h.2.2.2.1 s (mem_removeIdxs_1 hs), fun c hc => ?_, h.2.2.2.2.2⟩
  rcases List.mem_append.mp hc with hc | hc
  · exact h.2.2.2.2.1 c hc
  · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hc
    exact h.2.2.2.1 s (mem_removeIdxs_2 hs)

theorem Board.Good.detach {b b' : Board} {u : Nat} {w : PlayerId} {m : FieldMonster} (h : b.Good)
    (hd : b.detach u = some (b', w, m)) :
    b'.Good ∧ m.card.simple = true ∧ ∀ c ∈ m.overlays, c.simple = true := by
  unfold Board.detach at hd
  cases hf : b.findMonIdx u with
  | none => simp [hf] at hd
  | some wi =>
    obtain ⟨w0, i⟩ := wi
    cases hm : (b.get w0).monsters[i]? with
    | none => simp [hf, hm] at hd
    | some m0 =>
      simp only [hf, hm, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq,
        Prod.mk.injEq] at hd
      obtain ⟨rfl, rfl, rfl⟩ := hd
      have hp := h.get w0
      have h1 : (b.modify w0 fun p => { p with monsters := p.monsters.eraseIdx i }).Good :=
        h.modify w0 ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2.1,
          fun x hx => hp.2.2.2.2.2 x (List.mem_of_mem_eraseIdx hx)⟩
      refine ⟨?_, hp.2.2.2.2.2 m0 (List.mem_of_getElem? hm)⟩
      refine Board.Good.modifyP ?_ .two fun p hp => hp.dropEquips u
      exact Board.Good.modifyP h1 .one fun p hp => hp.dropEquips u

theorem Board.Good.toGraveMon {b : Board} (h : b.Good) (u : Nat) (cause : LeaveCause) :
    (b.toGraveMon u cause).Good := by
  unfold Board.toGraveMon
  split
  · exact h
  · rename_i b' w m hd
    obtain ⟨h', hmc, hmo⟩ := h.detach hd
    have hp := h'.get w
    have h1 : (b'.modify w fun p => { p with grave := p.grave ++ m.overlays ++ [.monster m.card] }).Good := by
      refine h'.modify w ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, fun c hc => ?_, hp.2.2.2.2.2⟩
      simp only [List.mem_append, List.mem_singleton] at hc
      rcases hc with (hc | hc) | rfl
      · exact hp.2.2.2.2.1 c hc
      · exact hmo c hc
      · exact hmc
    dsimp only
    split
    · exact h1.with_ _ rfl rfl
    · refine Board.Good.modifyP ?_ .two fun p hp => hp.removeBackrow _
      refine Board.Good.modifyP ?_ .one fun p hp => hp.removeBackrow _
      exact h1.with_ _ rfl rfl

theorem Board.Good.foldl_toGraveMon {α : Type} (xs : List α) (f : α → Nat) (cause : LeaveCause) {b : Board}
    (h : b.Good) : (xs.foldl (fun b x => b.toGraveMon (f x) cause) b).Good := by
  induction xs generalizing b with
  | nil => exact h
  | cons x xs ih => exact ih (h.toGraveMon _ _)

theorem Board.Good.foldl_toGraveMonN (us : List Nat) (cause : LeaveCause) {b : Board} (h : b.Good) :
    (us.foldl (fun b u => b.toGraveMon u cause) b).Good := h.foldl_toGraveMon us id cause

theorem Board.Good.destroyAllOf {b : Board} (h : b.Good) (w : PlayerId) : (b.destroyAllOf w).Good :=
  h.foldl_toGraveMon _ _ _

theorem Board.Good.destroyBackrow {b : Board} (h : b.Good) (w : PlayerId) (i : Nat) :
    (b.destroyBackrow w i).Good := by
  unfold Board.destroyBackrow
  split
  · exact h
  · rename_i s hs
    have hp := h.get w
    have h0 : (b.modify w fun p => { p with backrow := p.backrow.eraseIdx i, grave := p.grave ++ [s.card] }).Good := by
      refine h.modify w ⟨hp.1, hp.2.1, hp.2.2.1, fun x hx => hp.2.2.2.1 x (List.mem_of_mem_eraseIdx hx),
        fun c hc => ?_, hp.2.2.2.2.2⟩
      rcases List.mem_append.mp hc with hc | hc
      · exact hp.2.2.2.2.1 c hc
      · simp only [List.mem_singleton] at hc; subst hc; exact hp.2.2.2.1 s (List.mem_of_getElem? hs)
    simp only
    split
    · split
      · exact h0
      · exact h0.toGraveMon _ _
    · exact h0

theorem Board.Good.destroyAllBackrow {b : Board} (h : b.Good) (ws : List PlayerId) :
    (b.destroyAllBackrow ws).Good := by
  unfold Board.destroyAllBackrow
  simp only
  apply Board.Good.foldl_toGraveMonN
  generalize b = b0 at h
  induction ws generalizing b0 with
  | nil => exact h
  | cons w ws ih =>
    simp only [List.foldl]
    apply ih
    have hp := h.get w
    refine h.modify w ⟨hp.1, hp.2.1, hp.2.2.1, by simp, fun c hc => ?_, hp.2.2.2.2.2⟩
    rcases List.mem_append.mp hc with hc | hc
    · exact hp.2.2.2.2.1 c hc
    · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hc; exact hp.2.2.2.1 s hs

theorem Player.Good.drawOne {p p' : Player} (h : p.Good) (hd : p.drawOne = some p') : p'.Good := by
  unfold Player.drawOne at hd
  split at hd
  · simp at hd
  · rename_i c cs hdk
    simp only [Option.some.injEq] at hd
    subst hd
    have hc : ∀ x ∈ c :: cs, x.simple = true := hdk ▸ h.1
    refine ⟨fun x hx => hc x (List.mem_cons_of_mem _ hx), h.2.1, fun x hx => ?_, h.2.2.2⟩
    rcases List.mem_append.mp hx with hx | hx
    · exact h.2.2.1 x hx
    · simp only [List.mem_singleton] at hx; subst hx; exact hc _ List.mem_cons_self

theorem Player.Good.drawN {n : Nat} {p p' : Player} (h : p.Good) (hd : p.drawN n = some p') : p'.Good := by
  induction n generalizing p with
  | zero => simp [Player.drawN] at hd; subst hd; exact h
  | succ n ih =>
    simp only [Player.drawN, Option.bind_eq_some_iff] at hd
    obtain ⟨q, hq, hr⟩ := hd
    exact ih (h.drawOne hq) hr

theorem Player.Good.damage {p : Player} (h : p.Good) (n : Nat) : (p.damage n).Good := h
theorem Player.Good.heal {p : Player} (h : p.Good) (n : Nat) : (p.heal n).Good := h

/-! ### 効果 -/

/-- **効果を適用しても、どのカードも条件を満たす** -/
theorem Board.Good.applyEffect {b : Board} (h : b.Good) (c : Ctx) (l : ChainLink) : (applyEffect c l b).Good := by
  unfold YGO.applyEffect
  cases he : l.eff <;> simp only
  case noop => exact h
  case burn => exact h.modifyP _ fun p hp => hp.damage _
  case heal => exact h.modifyP _ fun p hp => hp.heal _
  case draw n =>
    split
    · exact h
    · rename_i p hp; exact h.set _ ((h.get _).drawN hp)
  case destroyOppMonsters => exact h.destroyAllOf _
  case destroyAllMonsters => exact (h.destroyAllOf _).destroyAllOf _
  case burnPerOppMonster => exact h.modifyP _ fun p hp => hp.damage _
  case negate n =>
    split
    · exact h
    · rename_i p hp; exact h.set _ ((h.get _).drawN hp)
  case destroyTarget => exact h.foldl_toGraveMonN _ _
  case revive own =>
    split
    · exact h
    · rename_i w i m hr
      have hg := reviveOk_grave hr
      have hm := (h.get w).2.2.2.2.1 _ (List.mem_of_getElem? hg)
      refine Board.Good.place ?_ _ hm _ _ _ _ (by simp)
      exact h.modifyP w fun p hp => ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1,
        fun x hx => hp.2.2.2.2.1 x (List.mem_of_mem_eraseIdx hx), hp.2.2.2.2.2⟩
  case fusionSummon =>
    split
    · exact h
    · rename_i fm i e hp
      have hx := fusionPlan_extra hp
      have hfm := (h.get l.owner).2.1 _ (List.mem_of_getElem? hx)
      have h1 : (b.modify l.owner fun p =>
          { p with hand := (removeIdxs p.hand (l.handMats.map (·.1))).1
                   grave := p.grave ++ (removeIdxs p.hand (l.handMats.map (·.1))).2 }).Good := by
        refine h.modifyP _ fun p hp => ⟨hp.1, hp.2.1, fun x hx => hp.2.2.1 x (mem_removeIdxs_1 hx),
          hp.2.2.2.1, fun x hx => ?_, hp.2.2.2.2.2⟩
        rcases List.mem_append.mp hx with hx | hx
        · exact hp.2.2.2.2.1 x hx
        · exact hp.2.2.1 x (mem_removeIdxs_2 hx)
      have h2 := h1.foldl_toGraveMonN l.fieldMats .sent
      split
      · refine Board.Good.place ?_ _ hfm _ _ _ _ (by simp)
        exact h2.modifyP _ fun p hp => ⟨hp.1, fun x hx => hp.2.1 x (List.mem_of_mem_eraseIdx hx),
          hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2.1, hp.2.2.2.2.2⟩
      · exact h2
  case destroyAttacker =>
    split
    · exact (h.toGraveMon _ _).with_ _ rfl rfl
    · exact h
  case negateAttack => exact h.with_ _ rfl rfl
  case destroyOppSpellTraps => exact h.destroyAllBackrow _
  case destroyAllSpellTraps => exact h.destroyAllBackrow _
  case destroySpellTrap =>
    split
    · split
      · exact h.destroyBackrow _ _
      · exact h
    · exact h
  case millOpp n =>
    exact h.modifyP _ fun p hp => ⟨fun x hx => hp.1 x (List.mem_of_mem_drop hx), hp.2.1, hp.2.2.1, hp.2.2.2.1,
      fun x hx => (List.mem_append.mp hx).elim (hp.2.2.2.2.1 x) (fun hx => hp.1 x (List.mem_of_mem_take hx)),
      hp.2.2.2.2.2⟩
  case recruit attr mx =>
    split
    next i _ =>
      split
      next m hm =>
        split
        · have hp := h.get l.owner
          have hmc := hp.1 _ (List.mem_of_getElem? hm)
          refine Board.Good.place ?_ _ hmc _ _ _ _ (by simp)
          exact h.set _ ⟨fun x hx => hp.1 x (List.mem_of_mem_eraseIdx hx), hp.2.1, hp.2.2.1, hp.2.2.2.1,
            hp.2.2.2.2.1, hp.2.2.2.2.2⟩
        · exact h
      next => exact h
    next => exact h
  case searchMaxDef d =>
    split
    next i _ =>
      split
      next cd hm =>
        have hp := h.get l.owner
        refine h.set _ ⟨fun x hx => hp.1 x (List.mem_of_mem_eraseIdx hx), hp.2.1, fun x hx => ?_, hp.2.2.2.1,
          hp.2.2.2.2.1, hp.2.2.2.2.2⟩
        rcases List.mem_append.mp hx with hx | hx
        · exact hp.2.2.1 x hx
        · simp only [List.mem_singleton] at hx; subst hx; exact hp.1 _ (List.mem_of_getElem? hm)
      next => exact h
    next => exact h

/-! ### チェーンの解決 -/

theorem Board.Good.toGrave {b : Board} (h : b.Good) {l : ChainLink} (hl : l.mon = false → l.card.simple = true) :
    (toGrave b l).Good := by
  unfold YGO.toGrave
  cases hm : l.mon
  · simp only [Bool.false_eq_true, ite_false]
    refine h.modifyP _ fun p hp => ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, fun x hx => ?_, hp.2.2.2.2.2⟩
    rcases List.mem_append.mp hx with hx | hx
    · exact hp.2.2.2.2.1 x hx
    · simp only [List.mem_singleton] at hx; subst hx; exact hl hm
  · simpa using h

theorem Board.Good.resolveLink {b : Board} (h : b.Good) (c : Ctx) {l : ChainLink}
    (hl : l.mon = false → l.card.simple = true) : (resolveLink c b l).Good := by
  have hA : (if b.effectNegated l then b else YGO.applyEffect c l b).Good := by
    split
    · exact h
    · exact h.applyEffect _ _
  unfold YGO.resolveLink
  simp only
  generalize (if b.effectNegated l then b else YGO.applyEffect c l b) = b1 at hA ⊢
  cases hm : l.mon
  · simp only [Bool.false_eq_true, ite_false]
    have hkeep : ∀ (eq bond : Option Nat),
        ({ b1.modify l.owner (fun p => { p with backrow := p.backrow ++
            [{ card := l.card, setTurn := c.turn, faceUp := true, equipTo := eq, bond,
               since := b1.clock + 1, id := b1.clock + 1 }] }) with clock := b1.clock + 1 } : Board).Good := by
      intro eq bond
      have : (b1.modify l.owner (fun p => { p with backrow := p.backrow ++
            [{ card := l.card, setTurn := c.turn, faceUp := true, equipTo := eq, bond,
               since := b1.clock + 1, id := b1.clock + 1 }] })).Good := by
        refine hA.modifyP l.owner fun p hp => ⟨hp.1, hp.2.1, hp.2.2.1, fun x hx => ?_,
          hp.2.2.2.2.1, hp.2.2.2.2.2⟩
        rcases List.mem_append.mp hx with hx | hx
        · exact hp.2.2.2.1 x hx
        · simp only [List.mem_singleton] at hx; subst hx; exact hl hm
      exact this.with_ _ rfl rfl
    have hg := hA.toGrave hl
    split
    · exact hkeep _ _
    · exact hkeep _ _
    · split
      · split
        · split
          · exact hg
          · exact hkeep _ _
        · exact hg
      · exact hg
    · exact hg
  · simpa using hA

theorem Board.Good.resolveChain {b : Board} (h : b.Good) (c : Ctx) {ls : List ChainLink} (hl : ChainGood ls)
    (neg : Bool) : (resolveChain c b neg ls).Good := by
  induction ls generalizing b neg with
  | nil => exact h
  | cons l rest ih =>
    simp only [YGO.resolveChain]
    have hl0 := hl l List.mem_cons_self
    have hr : ChainGood rest := fun x hx => hl x (List.mem_cons_of_mem _ hx)
    split
    · exact ih (h.toGrave hl0) hr _
    · exact ih (h.resolveLink c hl0) hr _

/-! ### 戦闘 -/

theorem Board.Good.iteTG {p : Prop} [Decidable p] {x : Board} (h : x.Good) (u : Nat) (c : LeaveCause) :
    (if p then x.toGraveMon u c else x).Good := by
  split
  · exact h.toGraveMon u c
  · exact h

theorem Board.Good.performBattle {b : Board} (h : b.Good) (c : Ctx) : (performBattle c b).Good := by
  unfold YGO.performBattle
  have hu : ∀ (b : Board), b.Good → ∀ (w : PlayerId) (u : Nat) (p : Prop) [Decidable p] (pos : Position) (since : Nat),
      (b.updMon w u fun x => if p then { x with pos, since } else x).Good :=
    fun b h w u p _ pos since => h.updMon w u _ fun x => by split <;> exact ⟨rfl, rfl⟩
  split
  · exact h
  · have h0 : ({ b with attack := none } : Board).Good := h.with_ _ rfl rfl
    dsimp only
    split
    · exact h0
    · split
      · exact h0
      · split
        · split
          · exact h0.modifyP _ fun p hp => hp.damage _
          · exact h0
        · split
          · exact h0
          · refine Board.Good.iteTG (Board.Good.iteTG ?_ _ _) _ _
            refine Board.Good.modifyP (Board.Good.modifyP ?_ _ fun p hp => hp.damage _) _ fun p hp => hp.damage _
            refine Board.Good.iteLog ?_
            refine Board.Good.updMon ?_ _ _ _ fun x => by split <;> exact ⟨rfl, rfl⟩
            exact Board.Good.iteClock h0

/-! ### 発動（チェーンに積む） -/

theorem mkLink_card {b : Board} {who : PlayerId} {card : Card} {eff : Effect} {speed : Nat}
    {args : Args} {shift : Option Nat} {l : ChainLink}
    (h : mkLink b who card eff speed args shift = .ok l) : l.card = card := by
  unfold mkLink at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals first | (cases h; rfl) | simp_all

theorem good_push {s s' : ChainState} {b : Board} {l : ChainLink} (hs : ChainGood s.chain) (hb : b.Good)
    (hl : l.mon = false → l.card.simple = true) (h : pushLink s b l = .ok s') : s'.Good := by
  obtain ⟨h1, h2⟩ := pushLink_ok h
  refine ⟨h1 ▸ hb, ?_⟩
  rw [h2]
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · exact hl
  · exact hs x hx

theorem good_activateSpellAct {c : Ctx} {s s' : ChainState} {hd : Nat} {args : Args} (hs : s.Good)
    (h : activateSpellAct c s hd args = .ok s') : s'.Good := by
  unfold activateSpellAct at h
  simp only [bind, Except.bind] at h
  repeat' split at h
  all_goals try (simp_all [throw, throwThe, MonadExceptOf.throw]; done)
  have hp := hs.1.get c.active
  have key : ∀ x, (s.board.get c.active).hand[hd]? = some x → x.simple = true :=
    fun x hx => hp.2.2.1 x (List.mem_of_getElem? hx)
  refine good_push hs.2 ?_ (fun _ => ?_) h
  · exact hs.1.set _ ⟨hp.1, hp.2.1, fun x hx => hp.2.2.1 x (List.mem_of_mem_eraseIdx hx), hp.2.2.2⟩
  · rw [mkLink_card (by assumption : mkLink _ _ _ _ _ _ _ = .ok _)]
    exact key _ (by assumption)

theorem good_activateSetAct {c : Ctx} {s s' : ChainState} {who : PlayerId} {z : Nat} {args : Args}
    (hs : s.Good) (h : activateSetAct c s who z args = .ok s') : s'.Good := by
  unfold activateSetAct at h
  simp only [bind, Except.bind] at h
  repeat' split at h
  all_goals try (simp_all [throw, throwThe, MonadExceptOf.throw]; done)
  all_goals
    have hp := hs.1.get who
    have key : ∀ x, (s.board.get who).backrow[z]? = some x → x.card.simple = true :=
      fun x hx => hp.2.2.2.1 x (List.mem_of_getElem? hx)
    refine good_push hs.2 ?_ (fun _ => ?_) h
    · refine Board.Good.modifyP ?_ _ fun p hp => hp.damage _
      exact hs.1.set _ ⟨hp.1, hp.2.1, hp.2.2.1, fun x hx => hp.2.2.2.1 x (List.mem_of_mem_eraseIdx hx),
        hp.2.2.2.2⟩
    · rw [mkLink_card (by assumption : mkLink _ _ _ _ _ _ _ = .ok _)]
      exact key _ (by assumption)

theorem good_activateMonsterAct {c : Ctx} {s s' : ChainState} {who : PlayerId} {z i : Nat} {args : Args}
    (hs : s.Good) (h : activateMonsterAct c s who z i args = .ok s') : s'.Good := by
  have key : ∀ m, (s.board.get who).monsters[z]? = some m →
      m.card.simple = true ∧ ∀ c ∈ m.overlays, c.simple = true :=
    fun m hm => (hs.1.get who).2.2.2.2.2 _ (List.mem_of_getElem? hm)
  unfold activateMonsterAct at h
  simp only [bind, Except.bind] at h
  repeat' split at h
  all_goals try (simp_all [throw, throwThe, MonadExceptOf.throw]; done)
  all_goals
    refine good_push hs.2 ?_ (fun hm => by simp at hm) h
    rename_i hv
    simp only [pure, Except.pure, Except.ok.injEq] at hv
    subst hv
    have km := key _ (by assumption)
  all_goals first
    | exact hs.1.setMonAt who z km
    | (refine Board.Good.toGraveMon ?_ _ _; exact hs.1.setMonAt who z km)
    | (refine Board.Good.modifyP ?_ _ fun p hp => hp.damage _; exact hs.1.setMonAt who z km)
    | (refine Board.Good.modifyP ?_ _ fun p hp => ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, fun x hx => ?_, hp.2.2.2.2.2⟩
       · refine Board.Good.setMonAt ?_ who z ?_
         · exact hs.1.setMonAt who z km
         · exact ⟨km.1, fun x hx => km.2 x (List.mem_of_mem_drop hx)⟩
       · rcases List.mem_append.mp hx with hx | hx
         · exact hp.2.2.2.2.1 x hx
         · exact km.2 x (List.mem_of_mem_take hx))

/-! ### 召喚・戦闘などの行動 -/

theorem Board.Good.withNS {b : Board} (h : b.Good) (x : Bool) : ({ b with normalSummoned := x } : Board).Good := h
theorem Board.Good.withAttack {b : Board} (h : b.Good) (a : Option AttackDecl) :
    ({ b with attack := a } : Board).Good := h

theorem Player.Good.eraseHand {p : Player} (h : p.Good) (i : Nat) :
    ({ p with hand := p.hand.eraseIdx i } : Player).Good :=
  ⟨h.1, h.2.1, fun x hx => h.2.2.1 x (List.mem_of_mem_eraseIdx hx), h.2.2.2⟩

theorem Player.Good.eraseExtra {p : Player} (h : p.Good) (i : Nat) :
    ({ p with extra := p.extra.eraseIdx i } : Player).Good :=
  ⟨h.1, fun x hx => h.2.1 x (List.mem_of_mem_eraseIdx hx), h.2.2⟩

theorem good_summonCore {c : Ctx} {b b' : Board} {hd : Nat} {ts : List Nat} {pos : Position} {sp : Bool}
    (hb : b.Good) (h : summonCore c b hd ts pos sp = .ok b') : b'.Good := by
  have key : ∀ x, (b.get c.active).hand[hd]? = some x → x.simple = true :=
    fun x hx => (hb.get c.active).2.2.1 x (List.mem_of_getElem? hx)
  unfold summonCore at h
  simp only [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  repeat' split at h
  all_goals try (cases h; done)
  all_goals
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    have hm := key _ (by assumption)
    refine Board.Good.withNS ?_ _
    refine Board.Good.place ?_ _ ?_ _ _ _ _ (by simp)
    · exact (hb.foldl_toGraveMon _ _ _).modifyP _ fun p hp => hp.eraseHand _
    · exact hm

theorem Board.Good.detachAllAux (ms : List FieldMonster) (acc : Board × List FieldMonster) (h : acc.1.Good)
    (ha : ∀ m ∈ acc.2, m.card.simple = true ∧ ∀ c ∈ m.overlays, c.simple = true) :
    (Board.detachAllAux acc ms).1.Good ∧
      ∀ m ∈ (Board.detachAllAux acc ms).2, m.card.simple = true ∧ ∀ c ∈ m.overlays, c.simple = true := by
  induction ms generalizing acc with
  | nil => exact ⟨h, ha⟩
  | cons m ms ih =>
    simp only [Board.detachAllAux]
    apply ih
    · split
      · rename_i b x hd; exact (h.detach hd).1
      · exact h
    · split
      · rename_i b x hd
        intro y hy
        rcases List.mem_append.mp hy with hy | hy
        · exact ha y hy
        · simp only [List.mem_singleton] at hy; subst hy; exact (h.detach hd).2
      · exact ha

theorem good_extraSummonAct {c : Ctx} {b b' : Board} {ei : Nat} {ms : List Nat} (hb : b.Good)
    (h : extraSummonAct c b ei ms = .ok b') : b'.Good := by
  have key : ∀ x, (b.get c.active).extra[ei]? = some x → x.simple = true :=
    fun x hx => (hb.get c.active).2.1 x (List.mem_of_getElem? hx)
  unfold extraSummonAct at h
  simp only [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  repeat' split at h
  all_goals try (cases h; done)
  all_goals simp only [pure, Except.pure, Except.ok.injEq] at h
  all_goals subst h
  all_goals have hem := key _ (by assumption)
  all_goals first
    | (refine Board.Good.place ?_ _ hem _ _ _ _ (by simp)
       exact (hb.foldl_toGraveMon _ _ _).modifyP _ fun p hp => hp.eraseExtra _)
    | (obtain ⟨hd1, hd2⟩ := Board.Good.detachAllAux _ (b, []) hb (by simp)
       refine Board.Good.place ?_ _ hem _ _ _ _ ?_
       · refine Board.Good.modifyP ?_ _ fun p hp => hp.eraseExtra _
         refine hd1.modifyP _ fun p hp => ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, fun x hx => ?_, hp.2.2.2.2.2⟩
         rcases List.mem_append.mp hx with hx | hx
         · exact hp.2.2.2.2.1 x hx
         · obtain ⟨m, hm, hx⟩ := List.mem_flatMap.mp hx
           exact (hd2 m hm).2 x hx
       · intro x hx
         obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hx
         exact (hd2 m hm).1)

theorem good_declareAttack {c : Ctx} {b b' : Board} {ai : Nat} {tg : Option Nat} (hb : b.Good)
    (h : declareAttack c b ai tg = .ok b') : b'.Good := by
  unfold declareAttack at h
  simp only [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  repeat' split at h
  all_goals try (cases h; done)
  all_goals simp only [pure, Except.pure, Except.ok.injEq] at h
  all_goals subst h
  all_goals
    refine Board.Good.withAttack ?_ _
    exact hb.updMon _ _ _ fun _ => ⟨rfl, rfl⟩

theorem good_changePositionAct {c : Ctx} {b b' : Board} {i : Nat} (hb : b.Good)
    (h : changePositionAct c b i = .ok b') : b'.Good := by
  unfold changePositionAct at h
  simp only [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  repeat' split at h
  all_goals try (cases h; done)
  all_goals simp only [pure, Except.pure, Except.ok.injEq] at h
  all_goals subst h
  all_goals exact hb.updMon _ _ _ fun _ => ⟨rfl, rfl⟩

theorem good_flipSummonAct {c : Ctx} {b b' : Board} {i : Nat} (hb : b.Good)
    (h : flipSummonAct c b i = .ok b') : b'.Good := by
  unfold flipSummonAct at h
  simp only [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  repeat' split at h
  all_goals try (cases h; done)
  all_goals simp only [pure, Except.pure, Except.ok.injEq] at h
  all_goals subst h
  all_goals exact hb.updMon _ _ _ fun _ => ⟨rfl, rfl⟩

theorem good_setSpellTrapAct {c : Ctx} {b b' : Board} {hd : Nat} (hb : b.Good)
    (h : setSpellTrapAct c b hd = .ok b') : b'.Good := by
  have key : ∀ x, (b.get c.active).hand[hd]? = some x → x.simple = true :=
    fun x hx => (hb.get c.active).2.2.1 x (List.mem_of_getElem? hx)
  unfold setSpellTrapAct at h
  simp only [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  repeat' split at h
  all_goals try (cases h; done)
  all_goals simp only [pure, Except.pure, Except.ok.injEq] at h
  all_goals subst h
  all_goals
    have hx := key _ (by assumption)
    have hp := hb.get c.active
    refine Board.Good.withClock ?_ _
    refine hb.set _ ⟨hp.1, hp.2.1, fun x hx => hp.2.2.1 x (List.mem_of_mem_eraseIdx hx),
      fun y hy => ?_, hp.2.2.2.2⟩
    rcases List.mem_append.mp hy with hy | hy
    · exact hp.2.2.2.1 y hy
    · simp only [List.mem_singleton] at hy; subst hy; exact hx

theorem good_discardAct {c : Ctx} {b b' : Board} {hd : Nat} (hb : b.Good)
    (h : discardAct c b hd = .ok b') : b'.Good := by
  have key : ∀ x, (b.get c.active).hand[hd]? = some x → x.simple = true :=
    fun x hx => (hb.get c.active).2.2.1 x (List.mem_of_getElem? hx)
  unfold discardAct at h
  simp only [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  repeat' split at h
  all_goals try (cases h; done)
  all_goals simp only [pure, Except.pure, Except.ok.injEq] at h
  all_goals subst h
  all_goals
    have hx := key _ (by assumption)
    have hp := hb.get c.active
    refine hb.set _ ⟨hp.1, hp.2.1, fun x hx => hp.2.2.1 x (List.mem_of_mem_eraseIdx hx), hp.2.2.2.1,
      fun y hy => ?_, hp.2.2.2.2.2⟩
    rcases List.mem_append.mp hy with hy | hy
    · exact hp.2.2.2.2.1 y hy
    · simp only [List.mem_singleton] at hy; subst hy; exact hx

theorem good_boardAct {c : Ctx} {b b' : Board} {a : Action} (hb : b.Good) (h : boardAct c b a = .ok b') :
    b'.Good := by
  cases a <;> simp only [boardAct] at h
  case normalSummon => exact good_summonCore hb h
  case normalSet => exact good_summonCore hb h
  case specialSummon => exact good_summonCore hb h
  case flipSummon => exact good_flipSummonAct hb h
  case changePosition => exact good_changePositionAct hb h
  case extraSummon => exact good_extraSummonAct hb h
  case setSpellTrap => exact good_setSpellTrapAct hb h
  case attack => exact good_declareAttack hb h
  case discard => exact good_discardAct hb h
  all_goals cases h

theorem good_passAct (c : Ctx) {s : ChainState} (hs : s.Good) : (passAct c s).Good := by
  unfold passAct
  split
  · split
    · exact ⟨hs.1.performBattle c, by simp [ChainGood]⟩
    · exact ⟨hs.1.resolveChain c hs.2 false, by simp [ChainGood]⟩
  · exact hs

theorem good_act {c : Ctx} {s s' : ChainState} {a : Action} (hs : s.Good) (h : act c s a = .ok s') :
    s'.Good := by
  cases a <;> simp only [act] at h
  case pass => simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; exact good_passAct c hs
  case activateSpell => exact good_activateSpellAct hs h
  case activateSet => exact good_activateSetAct hs h
  case activateMonster => exact good_activateMonsterAct hs h
  all_goals try simp only [throw, throwThe, MonadExceptOf.throw] at h
  all_goals repeat' split at h
  all_goals try (cases h; done)
  all_goals
    obtain ⟨b, hb, rfl⟩ := Except.map_ok h
    exact ⟨good_boardAct hs.1 hb, hs.2⟩

theorem good_processTriggers (c : Ctx) {s : ChainState} (hs : s.Good) : (processTriggers c s).Good := by
  unfold processTriggers
  split
  · exact hs
  · dsimp only
    split
    · exact ⟨hs.1.withLog _, hs.2⟩
    · refine ⟨hs.1.withLog _, fun l hl hm => ?_⟩
      simp only [List.mem_reverse, List.mem_append, List.mem_filter, List.mem_flatMap] at hl
      have : l.mon = true := by
        rcases hl with ⟨⟨h, _, hl⟩, _⟩ | ⟨⟨h, _, hl⟩, _⟩ <;> exact triggeredLinks_mon hl
      rw [hm] at this; cases this

theorem good_nextPhase {g g' : Game} (hg : g.Good) (h : nextPhase g = .ok g') : g'.Good := by
  have hr : ∀ p : Player, p.Good → p.resetMonsters.Good := fun p hp => hp.mapMon _ fun _ => ⟨rfl, rfl⟩
  unfold nextPhase at h
  split at h
  all_goals try (simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; exact hg)
  · split at h <;> (simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; exact hg)
  · split at h
    · cases h
    · dsimp only at h
      have hb : ((({ g.board with normalSummoned := false, turnPlayer := g.active.other } : Board).modify g.active
          Player.resetMonsters).modify g.active.other Player.resetMonsters).Good := by
        refine Board.Good.modifyP (Board.Good.modifyP ?_ _ hr) _ hr
        exact hg.1.with_ _ rfl rfl
      split at h
      · simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
        exact ⟨hb, hg.2⟩
      · rename_i p hp
        simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
        exact ⟨hb.set _ ((hb.get _).drawOne hp), hg.2⟩

/-! ### 永続効果の判定結果の書き込み -/

theorem FieldMonster.commitAura_card (r : List AuraSrc) (m : FieldMonster) : (m.commitAura r).card = m.card := by
  unfold FieldMonster.commitAura; split <;> rfl

theorem SetCard.commitAura_card (r : List AuraSrc) (k : Nat × Nat × Nat) (c : SetCard) :
    (c.commitAura r k).card = c.card := by
  unfold SetCard.commitAura; split <;> rfl

theorem Player.Good.commitAuras {p : Player} (h : p.Good) (w : PlayerId) (r : List AuraSrc) :
    (p.commitAuras w r).Good := by
  refine ⟨h.1, h.2.1, h.2.2.1, fun s hs => ?_, h.2.2.2.2.1, fun m hm => ?_⟩
  · simp only [Player.commitAuras, List.mem_mapIdx] at hs
    obtain ⟨i, hi, rfl⟩ := hs
    rw [SetCard.commitAura_card]
    exact h.2.2.2.1 _ (List.getElem_mem hi)
  · simp only [Player.commitAuras, List.mem_map] at hm
    obtain ⟨m0, hm0, rfl⟩ := hm
    rw [FieldMonster.commitAura_card, FieldMonster.commitAura_overlays]
    exact h.2.2.2.2.2 m0 hm0

theorem Board.Good.commitAuras {b : Board} (h : b.Good) : b.commitAuras.Good :=
  ⟨h.1.commitAuras _ _, h.2.commitAuras _ _⟩

theorem Board.Good.chooseAura {b b' : Board} {i : Nat} (h : b.Good) (hc : b.chooseAura i = .ok b') : b'.Good := by
  obtain ⟨r, t, rfl⟩ := Board.chooseAura_ok hc
  exact ⟨h.1.commitAuras _ _, h.2.commitAuras _ _⟩

/-- **1手進めても、どのカードも条件を満たす** -/
theorem step_good {g g' : Game} {a : Action} (hg : g.Good) (h : step g a = .ok g') : g'.Good := by
  unfold step at h
  split at h
  · cases h
  split at h
  · obtain ⟨i, b, -, hb, rfl⟩ := chooseStep_ok h
    exact ⟨(hg.1.chooseAura hb).commitAuras, hg.2⟩
  · split at h
    · split at h
      · exact good_nextPhase hg h
      · cases h
    · cases ha : act g.ctx g.cs a <;> simp only [ha, Except.map] at h
      · cases h
      · rename_i s0
        simp only [Except.ok.injEq] at h; subst h
        have h1 := good_act (s := g.cs) ⟨hg.1, hg.2⟩ ha
        have h2 := good_processTriggers g.ctx (s := { s0 with board := s0.board.commitAuras })
          ⟨h1.1.commitAuras, h1.2⟩
        exact h2

/-! ## 盤面のカードは条件を満たす -/

theorem Player.Good.sources_simple {p : Player} (h : p.Good) (w : PlayerId) :
    ∀ s ∈ p.sources w, s.Simple := by
  intro s hs
  rw [AuraSrc.simple_iff]
  unfold Player.sources at hs
  rcases List.mem_append.mp hs with hs | hs
  · obtain ⟨i, -, hi⟩ := List.mem_filterMap.mp hs
    split at hi
    · rename_i sc hsc
      split at hi
      · simp only [Option.some.injEq] at hi
        subst hi
        exact Card.stSimple_of (h.2.2.2.1 sc (List.mem_of_getElem? hsc))
      · cases hi
    · cases hi
  · obtain ⟨m, hm, hi⟩ := List.mem_filterMap.mp hs
    split at hi
    · cases hi
    · simp only [Option.some.injEq] at hi
      subst hi
      exact (h.2.2.2.2.2 m hm).1

/-- **どのカードも条件を満たす盤面では、永続効果を持つカードは `AuraSrc.Simple` を満たす** -/
theorem Board.Good.sources_simple {b : Board} (h : b.Good) : ∀ s ∈ b.sources, s.Simple := by
  intro s hs
  rcases List.mem_append.mp hs with hs | hs
  · exact h.1.sources_simple .one s hs
  · exact h.2.sources_simple .two s hs

/-! ## デッキのカードから導く -/

/-- 初期状態：デッキ・エクストラデッキのカードがすべて条件を満たせば、どのカードも条件を満たす -/
theorem Game.init_good {d1 d2 e1 e2 : List Card} (h1 : ∀ c ∈ d1, c.simple = true) (h2 : ∀ c ∈ d2, c.simple = true)
    (h3 : ∀ c ∈ e1, c.simple = true) (h4 : ∀ c ∈ e2, c.simple = true) : (Game.init d1 d2 e1 e2).Good := by
  have e : ∀ c ∈ ([] : List Card), c.simple = true := by simp
  refine ⟨⟨⟨fun c hc => h1 c (List.mem_of_mem_drop hc), h3, fun c hc => h1 c (List.mem_of_mem_take hc),
      by simp [Game.init], e, by simp [Game.init]⟩,
    ⟨fun c hc => h2 c (List.mem_of_mem_drop hc), h4, fun c hc => h2 c (List.mem_of_mem_take hc),
      by simp [Game.init], e, by simp [Game.init]⟩⟩, by simp [ChainGood, Game.init]⟩

/-- デッキ・エクストラデッキのカードがすべて条件を満たす対戦で、合法な手順で到達可能な状態 -/
inductive SimpleReachable : Game → Prop
  | init (d1 d2 e1 e2 : List Card) : (∀ c ∈ d1 ++ d2 ++ e1 ++ e2, c.simple = true) →
      SimpleReachable (Game.init d1 d2 e1 e2)
  | step {g g' : Game} (a : Action) : SimpleReachable g → step g a = .ok g' → SimpleReachable g'

theorem SimpleReachable.reachable {g : Game} (h : SimpleReachable g) : Reachable g := by
  induction h with
  | init d1 d2 e1 e2 _ => exact .init d1 d2 e1 e2
  | step a _ hs ih => exact .step a ih hs

theorem SimpleReachable.good {g : Game} (h : SimpleReachable g) : g.Good := by
  induction h with
  | init d1 d2 e1 e2 hc =>
    simp only [List.mem_append] at hc
    exact Game.init_good (fun c h => hc c (.inl (.inl (.inl h)))) (fun c h => hc c (.inl (.inl (.inr h))))
      (fun c h => hc c (.inl (.inr h))) (fun c h => hc c (.inr h))
  | step a _ hs ih => exact step_good ih hs

/-- **デッキとエクストラデッキのカードがすべて条件を満たせば、対戦の途中のどの盤面でも、
永続効果の判定は必ず止まる**（決まっているか、選択待ち） -/
theorem simpleReachable_settled {g : Game} (hr : SimpleReachable g) :
    settleOnce (settle g.board.sources g.board.clock g.board.turnPlayer).1
      (settle g.board.sources g.board.clock g.board.turnPlayer).2 g.board.turnPlayer = none :=
  reachable_settled hr.reachable hr.good.1.sources_simple

/-- **同じく、有効なカード同士は互いに無効にしない** -/
theorem simpleReachable_consistent {g : Game} (hr : SimpleReachable g) {s t : AuraSrc}
    (hs : s ∈ g.board.effective) (ht : t ∈ g.board.effective) : t.beats s = false :=
  reachable_consistent hr.reachable hr.good.1.sources_simple hs ht

/-! ## 今あるカード -/

open Cards in
/-- D－HERO Bloo－D 以外の、今あるカード例 -/
def simpleCards : List Card :=
  [.monster blueEyes, .monster darkMagician, .monster redEyes, .monster summonedSkull,
   .monster celticGuardian, .monster giantSoldier, .monster mysticalElf, .monster kuriboh,
   .monster tuneWarrior, .monster commandKnight, .monster exiledForce, .monster needleWorm,
   .monster killerTomato, .monster giantRat, .monster witch, .monster sacredCrane, .monster jinzo,
   .monster bSkullDragon, .monster gaiaKnight, .monster hope, .monster proxyDragon, potOfGreed, raigeki,
   darkHole, hinotama, ookazi, dianKeto, monsterReborn, polymerization, axeOfDespair, burdenOfMighty,
   harpieFeather, heavyStorm, cyclone, justDesserts, darkBribe, sakuretsu, gravityBind, skillDrain,
   royalDecree, callOfHaunted]

-- これらはすべて条件を満たす。D－HERO Bloo－D は満たさない
example : ∀ c ∈ simpleCards, c.simple = true := by decide
example : (Card.monster Cards.bloo).simple = false := by decide

end YGO

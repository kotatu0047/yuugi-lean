import YuugiLean.YuGiOh

/-!
# 不変条件

`step` で1手進めても保たれる性質を証明する。

* カードの総数は変わらない（`step_count`）
-/

namespace YGO

/-! ## カードの総数 -/

/-- フィールドのモンスターの枚数（X素材を含む） -/
def monCount (ms : List FieldMonster) : Nat := (ms.map fun m => m.overlays.length + 1).sum

def Player.count (p : Player) : Nat :=
  p.deck.length + p.extra.length + p.hand.length + p.backrow.length + p.grave.length +
    monCount p.monsters

def Board.count (b : Board) : Nat := b.p1.count + b.p2.count

/-- チェーン上の魔法・罠カードの枚数（モンスター効果のブロックはカードを持たない） -/
def nonMon (ch : List ChainLink) : Nat := (ch.filter (fun l => !l.mon)).length

def ChainState.count (s : ChainState) : Nat := s.board.count + nonMon s.chain

def Game.count (g : Game) : Nat := g.board.count + nonMon g.chain

/-! ### リストの補題 -/

theorem length_eraseIdx_of_getElem? {α : Type} {l : List α} {i : Nat} {x : α} (h : l[i]? = some x) :
    (l.eraseIdx i).length + 1 = l.length := by
  have : i < l.length := by
    rcases List.getElem?_eq_some_iff.mp h with ⟨hi, _⟩; exact hi
  rw [List.length_eraseIdx_of_lt this]; omega

theorem length_filter_add_not {α : Type} (l : List α) (p : α → Bool) :
    (l.filter p).length + (l.filter (fun x => !p x)).length = l.length := by
  induction l with
  | nil => rfl
  | cons x xs ih => cases h : p x <;> simp [h] <;> omega

theorem monCount_append (l l' : List FieldMonster) : monCount (l ++ l') = monCount l + monCount l' := by
  simp [monCount]

theorem monCount_eraseIdx {l : List FieldMonster} {i : Nat} {m : FieldMonster} (h : l[i]? = some m) :
    monCount (l.eraseIdx i) + m.overlays.length + 1 = monCount l := by
  induction l generalizing i with
  | nil => simp at h
  | cons x xs ih =>
    cases i with
    | zero => simp at h; subst h; simp [monCount]; omega
    | succ j => simp at h; have := ih h; simp [monCount] at this ⊢; omega

theorem monCount_set {l : List FieldMonster} {i : Nat} {m m' : FieldMonster} (h : l[i]? = some m) :
    monCount (l.set i m') + m.overlays.length = monCount l + m'.overlays.length := by
  induction l generalizing i with
  | nil => simp at h
  | cons x xs ih =>
    cases i with
    | zero => simp at h; subst h; simp [monCount]; omega
    | succ j => simp at h; have := ih h; simp [monCount] at this ⊢; omega

theorem monCount_map {l : List FieldMonster} {f : FieldMonster → FieldMonster}
    (hf : ∀ x, (f x).overlays = x.overlays) : monCount (l.map f) = monCount l := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [monCount] at ih ⊢; rw [hf, ih]

/-! ### 盤面の補題 -/

theorem Board.count_modify (b : Board) (w : PlayerId) (f : Player → Player) :
    (b.modify w f).count + (b.get w).count = b.count + (f (b.get w)).count := by
  cases w <;> simp [Board.modify, Board.set, Board.get, Board.count] <;> omega

theorem Board.count_modify_eq (b : Board) (w : PlayerId) (f : Player → Player)
    (hf : (f (b.get w)).count = (b.get w).count) : (b.modify w f).count = b.count := by
  have := b.count_modify w f; omega

theorem Board.count_set (b : Board) (w : PlayerId) (p : Player) :
    (b.set w p).count + (b.get w).count = b.count + p.count := by
  cases w <;> simp [Board.set, Board.get, Board.count] <;> omega

theorem Board.get_modify_same (b : Board) (w : PlayerId) (f : Player → Player) :
    (b.modify w f).get w = f (b.get w) := by
  cases w <;> rfl

theorem Board.get_modify_other (b : Board) (w v : PlayerId) (f : Player → Player) (h : v ≠ w) :
    (b.modify w f).get v = b.get v := by
  cases w <;> cases v <;> simp_all [Board.modify, Board.set, Board.get]

theorem Board.count_place (b : Board) (w : PlayerId) (c : MonsterCard) (pos : Position) (t : Nat)
    (emz : Bool) (ev : Option Event) (ov : List Card) :
    (b.place w c pos t emz ev ov).count = b.count + ov.length + 1 := by
  cases w <;> simp [Board.place, Board.modify, Board.set, Board.get, Board.count, Player.count,
    monCount] <;> omega

theorem Board.count_updMon (b : Board) (w : PlayerId) (u : Nat) (f : FieldMonster → FieldMonster)
    (hf : ∀ x, (f x).overlays = x.overlays) : (b.updMon w u f).count = b.count := by
  unfold Board.updMon
  apply Board.count_modify_eq
  simp only [Player.count]
  rw [monCount_map (f := fun m => if m.uid = u then f m else m)]
  intro x; split <;> simp [hf]

theorem Board.count_setMonAt (b : Board) (w : PlayerId) (i : Nat) (m m' : FieldMonster)
    (h : (b.get w).monsters[i]? = some m) :
    (b.setMonAt w i m').count + m.overlays.length = b.count + m'.overlays.length := by
  unfold Board.setMonAt
  have := b.count_modify w (fun p => { p with monsters := p.monsters.set i m' })
  have hs := monCount_set (m' := m') h
  simp only [Player.count] at this ⊢
  omega

theorem Board.count_attack (b : Board) (a : Option AttackDecl) : { b with attack := a }.count = b.count := rfl
theorem Board.count_log (b : Board) (l : List Happened) : { b with log := l }.count = b.count := rfl
theorem Board.count_clock (b : Board) (n : Nat) : { b with clock := n }.count = b.count := rfl
theorem Board.count_ns (b : Board) (x : Bool) : { b with normalSummoned := x }.count = b.count := rfl

/-- 装備カードを墓地へ送っても枚数は変わらない -/
theorem Player.count_dropEquips (p : Player) (u : Nat) :
    ({ p with backrow := p.backrow.filter (·.equipTo != some u)
              grave := p.grave ++ (p.backrow.filter (·.equipTo == some u)).map (·.card) } : Player).count
      = p.count := by
  have := length_filter_add_not p.backrow (fun s => s.equipTo == some u)
  simp only [Player.count, List.length_append, List.length_map] at this ⊢
  simp only [bne] at *
  omega

theorem Board.count_detach {b b' : Board} {u : Nat} {w : PlayerId} {m : FieldMonster}
    (h : b.detach u = some (b', w, m)) : b'.count + m.overlays.length + 1 = b.count := by
  unfold Board.detach at h
  cases hf : b.findMonIdx u with
  | none => simp [hf] at h
  | some wi =>
    obtain ⟨w0, i⟩ := wi
    cases hm : (b.get w0).monsters[i]? with
    | none => simp [hf, hm] at h
    | some m0 =>
      simp only [hf, hm, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq,
        Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      rw [Board.count_modify_eq _ _ _ (Player.count_dropEquips _ u),
          Board.count_modify_eq _ _ _ (Player.count_dropEquips _ u)]
      have h1 := b.count_modify w0 (fun p => { p with monsters := p.monsters.eraseIdx i })
      have h2 := monCount_eraseIdx hm
      simp only [Player.count] at h1 ⊢
      omega

theorem Player.count_removeBackrow (p : Player) (is : List Nat) :
    ({ p with backrow := (removeIdxs p.backrow is).1
              grave := p.grave ++ (removeIdxs p.backrow is).2.map (·.card) } : Player).count = p.count := by
  have := removeIdxs_length p.backrow is
  simp only [Player.count, List.length_append, List.length_map] at this ⊢
  omega

theorem Board.count_toGraveMon (b : Board) (u : Nat) (cause : LeaveCause) :
    (b.toGraveMon u cause).count = b.count := by
  unfold Board.toGraveMon
  split
  · rfl
  · rename_i b' w m hd
    have hdc := Board.count_detach hd
    have hg := b'.count_modify w (fun p => { p with grave := p.grave ++ m.overlays ++ [.monster m.card] })
    simp only [Player.count, List.length_append, List.length_cons, List.length_nil] at hg
    by_cases hc : (cause == LeaveCause.sent) = true
    · simp only [hc, ite_true]
      simp only [Board.count] at hg hdc ⊢; omega
    · simp only [hc, Bool.false_eq_true, ite_false]
      rw [Board.count_modify_eq _ _ _ (Player.count_removeBackrow _ _),
          Board.count_modify_eq _ _ _ (Player.count_removeBackrow _ _)]
      simp only [Board.count] at hg hdc ⊢; omega

theorem Board.count_foldl_toGraveMon (us : List Nat) (cause : LeaveCause) (b : Board) :
    (us.foldl (fun b u => b.toGraveMon u cause) b).count = b.count := by
  induction us generalizing b with
  | nil => rfl
  | cons u us ih => simp only [List.foldl]; rw [ih, Board.count_toGraveMon]

theorem Board.count_foldl_toGraveMon' {α : Type} (xs : List α) (f : α → Nat) (cause : LeaveCause) (b : Board) :
    (xs.foldl (fun b x => b.toGraveMon (f x) cause) b).count = b.count := by
  induction xs generalizing b with
  | nil => rfl
  | cons x xs ih => simp only [List.foldl]; rw [ih, Board.count_toGraveMon]

theorem Board.count_destroyAllOf (b : Board) (w : PlayerId) : (b.destroyAllOf w).count = b.count := by
  unfold Board.destroyAllOf
  exact Board.count_foldl_toGraveMon' _ _ _ _

theorem Board.count_destroyAllBackrow (b : Board) (ws : List PlayerId) :
    (b.destroyAllBackrow ws).count = b.count := by
  unfold Board.destroyAllBackrow
  simp only
  rw [Board.count_foldl_toGraveMon]
  generalize b = b0
  induction ws generalizing b0 with
  | nil => rfl
  | cons w ws ih =>
    simp only [List.foldl]
    rw [ih]
    apply Board.count_modify_eq
    simp [Player.count]; omega

theorem Player.count_drawOne {p p' : Player} (h : p.drawOne = some p') : p'.count = p.count := by
  unfold Player.drawOne at h
  split at h
  · simp at h
  · simp at h; subst h; simp_all [Player.count]; omega

theorem Player.count_drawN {n : Nat} {p p' : Player} (h : p.drawN n = some p') : p'.count = p.count := by
  induction n generalizing p with
  | zero => simp [Player.drawN] at h; subst h; rfl
  | succ n ih =>
    simp only [Player.drawN, Option.bind_eq_some_iff] at h
    obtain ⟨q, hq, hr⟩ := h
    rw [ih hr, Player.count_drawOne hq]

theorem Player.count_damage (p : Player) (n : Nat) : (p.damage n).count = p.count := rfl
theorem Player.count_heal (p : Player) (n : Nat) : (p.heal n).count = p.count := rfl

/-! ### 変わらない部分（LP・デッキ・エクストラデッキ・手札） -/

/-- LP・デッキ・エクストラデッキ・手札が同じ -/
def Player.Frame (p q : Player) : Prop :=
  q.lp = p.lp ∧ q.deck = p.deck ∧ q.extra = p.extra ∧ q.hand = p.hand

def Board.Frame (b b' : Board) : Prop := ∀ v, (b.get v).Frame (b'.get v)

theorem Board.Frame.refl (b : Board) : b.Frame b := fun _ => ⟨rfl, rfl, rfl, rfl⟩

theorem Board.Frame.trans {b b' b'' : Board} (h1 : b.Frame b') (h2 : b'.Frame b'') : b.Frame b'' :=
  fun v => by
    obtain ⟨a1, a2, a3, a4⟩ := h1 v
    obtain ⟨c1, c2, c3, c4⟩ := h2 v
    exact ⟨c1.trans a1, c2.trans a2, c3.trans a3, c4.trans a4⟩

theorem Board.Frame.modify (b : Board) (w : PlayerId) (f : Player → Player)
    (hf : (b.get w).Frame (f (b.get w))) : b.Frame (b.modify w f) := by
  intro v
  by_cases hv : v = w
  · subst hv; rw [Board.get_modify_same]; exact hf
  · rw [Board.get_modify_other _ _ _ _ hv]; exact ⟨rfl, rfl, rfl, rfl⟩

theorem Board.Frame.with (b : Board) (b' : Board) (h1 : b'.p1 = b.p1) (h2 : b'.p2 = b.p2) :
    b.Frame b' := by
  intro v; cases v <;> simp [Board.get, h1, h2] <;> exact ⟨rfl, rfl, rfl, rfl⟩

theorem Board.frame_modify (b : Board) (w : PlayerId) (f : Player → Player)
    (hf : ∀ p : Player, p.Frame (f p)) : b.Frame (b.modify w f) :=
  Board.Frame.modify b w f (hf _)

theorem Board.frame_detach {b b' : Board} {u : Nat} {w : PlayerId} {m : FieldMonster}
    (h : b.detach u = some (b', w, m)) : b.Frame b' := by
  unfold Board.detach at h
  cases hf : b.findMonIdx u with
  | none => simp [hf] at h
  | some wi =>
    obtain ⟨w0, i⟩ := wi
    cases hm : (b.get w0).monsters[i]? with
    | none => simp [hf, hm] at h
    | some m0 =>
      simp only [hf, hm, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq,
        Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      intro v
      cases v <;> cases w0 <;> simp [Board.modify, Board.set, Board.get, Player.Frame]

theorem Board.frame_toGraveMon (b : Board) (u : Nat) (cause : LeaveCause) :
    b.Frame (b.toGraveMon u cause) := by
  unfold Board.toGraveMon
  split
  · exact Board.Frame.refl _
  · rename_i b' w m hd
    refine (Board.frame_detach hd).trans ?_
    intro v
    by_cases hc : (cause == LeaveCause.sent) = true
    · simp only [hc, ite_true]
      cases v <;> cases w <;> simp [Board.modify, Board.set, Board.get, Player.Frame]
    · simp only [hc, Bool.false_eq_true, ite_false]
      cases v <;> cases w <;> simp [Board.modify, Board.set, Board.get, Player.Frame]

theorem Board.frame_foldl_toGraveMon {α : Type} (xs : List α) (f : α → Nat) (cause : LeaveCause)
    (b : Board) : b.Frame (xs.foldl (fun b x => b.toGraveMon (f x) cause) b) := by
  induction xs generalizing b with
  | nil => exact Board.Frame.refl _
  | cons x xs ih => exact (Board.frame_toGraveMon _ _ _).trans (ih _)

theorem Board.frame_foldl_toGraveMonN (us : List Nat) (cause : LeaveCause) (b : Board) :
    b.Frame (us.foldl (fun b u => b.toGraveMon u cause) b) :=
  Board.frame_foldl_toGraveMon us id cause b

/-! ### 効果 -/

theorem reviveOk_grave {b : Board} {l : ChainLink} {w : PlayerId} {i : Nat} {m : MonsterCard}
    (h : reviveOk b l = some (w, i, m)) : (b.get w).grave[i]? = some (.monster m) := by
  unfold reviveOk at h
  split at h
  · split at h
    · rename_i hc; simp at h; obtain ⟨rfl, rfl, rfl, rfl⟩ := h; exact hc.1
    · simp at h
  · simp at h

theorem fusionPlan_extra {b : Board} {l : ChainLink} {fm : MonsterCard} {i : Nat} {e : Bool}
    (h : fusionPlan b l = some (fm, i, e)) : (b.get l.owner).extra[i]? = some (.monster fm) := by
  unfold fusionPlan at h
  split at h
  · split at h
    · rename_i hc
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨_, _, he⟩ := h
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl, _⟩ := he
      exact hc
    · simp at h
  · simp at h

theorem Board.count_set_eq (b : Board) (w : PlayerId) (p : Player) (hp : p.count = (b.get w).count) :
    (b.set w p).count = b.count := by
  have := b.count_set w p; omega

/-- **効果を適用してもカードの総数は変わらない** -/
theorem Board.count_applyEffect (c : Ctx) (l : ChainLink) (b : Board) :
    (applyEffect c l b).count = b.count := by
  unfold applyEffect
  cases he : l.eff <;> simp only
  case burn => exact Board.count_modify_eq _ _ _ rfl
  case heal => exact Board.count_modify_eq _ _ _ rfl
  case draw n =>
    split
    · rfl
    · rename_i p hp; exact Board.count_set_eq _ _ _ (Player.count_drawN hp)
  case destroyOppMonsters => exact Board.count_destroyAllOf _ _
  case destroyAllMonsters => rw [Board.count_destroyAllOf, Board.count_destroyAllOf]
  case burnPerOppMonster => exact Board.count_modify_eq _ _ _ rfl
  case negate n =>
    split
    · rfl
    · rename_i p hp; exact Board.count_set_eq _ _ _ (Player.count_drawN hp)
  case destroyTarget => exact Board.count_foldl_toGraveMon _ _ _
  case revive own =>
    split
    · rfl
    · rename_i w i m hr
      rw [Board.count_place]
      have h1 := b.count_modify w (fun p => { p with grave := p.grave.eraseIdx i })
      have h2 := length_eraseIdx_of_getElem? (reviveOk_grave hr)
      simp only [Player.count] at h1
      simp; omega
  case fusionSummon =>
    split
    · rfl
    · rename_i fm i e hp
      have hx := fusionPlan_extra hp
      -- 手札の素材を墓地へ
      have h1 := b.count_modify l.owner (fun p =>
        { p with hand := (removeIdxs p.hand (l.handMats.map (·.1))).1
                 grave := p.grave ++ (removeIdxs p.hand (l.handMats.map (·.1))).2 })
      have h1' := removeIdxs_length (b.get l.owner).hand (l.handMats.map (·.1))
      simp only [Player.count, List.length_append] at h1
      generalize hb1 : b.modify l.owner _ = b1 at h1
      -- フィールドの素材を墓地へ
      have h2 := Board.count_foldl_toGraveMon l.fieldMats LeaveCause.sent b1
      have hf2 := Board.frame_foldl_toGraveMonN l.fieldMats LeaveCause.sent b1
      generalize hb2 : l.fieldMats.foldl _ b1 = b2 at h2 hf2
      have hf1 : (b1.get l.owner).extra = (b.get l.owner).extra := by
        rw [← hb1, Board.get_modify_same]
      have hx2 : (b2.get l.owner).extra[i]? = some (.monster fm) := by
        rw [(hf2 l.owner).2.2.1, hf1]; exact hx
      split
      · rw [Board.count_place]
        have h3 := b2.count_modify l.owner (fun p => { p with extra := p.extra.eraseIdx i })
        have h4 := length_eraseIdx_of_getElem? hx2
        simp only [Player.count] at h3
        simp; omega
      · omega
  case destroyAttacker =>
    split
    · exact Board.count_toGraveMon _ _ _
    · rfl
  case negateAttack => rfl
  case destroyOppSpellTraps => exact Board.count_destroyAllBackrow _ _
  case destroyAllSpellTraps => exact Board.count_destroyAllBackrow _ _
  case millOpp n =>
    apply Board.count_modify_eq
    simp [Player.count]; omega
  case recruit attr mx =>
    split
    next i _ =>
      split
      next m hm =>
        split
        · rw [Board.count_place]
          have h1 := b.count_set l.owner { b.get l.owner with deck := (b.get l.owner).deck.eraseIdx i }
          have h2 := length_eraseIdx_of_getElem? hm
          simp only [Player.count] at h1
          simp; omega
        · rfl
      next => rfl
    next => rfl
  case searchMaxDef d =>
    split
    next i _ =>
      split
      next cd hm =>
        have h1 := b.count_set l.owner
          { b.get l.owner with deck := (b.get l.owner).deck.eraseIdx i, hand := (b.get l.owner).hand ++ [cd] }
        have h2 := length_eraseIdx_of_getElem? hm
        simp only [Player.count, List.length_append, List.length_cons, List.length_nil] at h1
        omega
      next => rfl
    next => rfl

/-! ### チェーンの解決 -/

def linkCards (l : ChainLink) : Nat := if l.mon then 0 else 1

theorem nonMon_cons (l : ChainLink) (ls : List ChainLink) : nonMon (l :: ls) = linkCards l + nonMon ls := by
  unfold nonMon linkCards; cases hm : l.mon <;> simp [hm]; omega

theorem Board.count_toGrave (b : Board) (l : ChainLink) : (toGrave b l).count = b.count + linkCards l := by
  unfold toGrave linkCards
  cases hm : l.mon
  · simp only [Bool.false_eq_true, ite_false]
    have := b.count_modify l.owner (fun p => { p with grave := p.grave ++ [l.card] })
    simp [Player.count] at this; omega
  · simp

theorem Board.count_resolveLink (c : Ctx) (b : Board) (l : ChainLink) :
    (resolveLink c b l).count = b.count + linkCards l := by
  have hA : (if b.effectNegated l then b else applyEffect c l b).count = b.count := by
    split
    · rfl
    · exact Board.count_applyEffect _ _ _
  unfold resolveLink
  simp only
  generalize hb1 : (if b.effectNegated l then b else applyEffect c l b) = b1 at hA
  cases hm : l.mon
  · simp only [Bool.false_eq_true, ite_false]
    have hkeep : ∀ (eq bond : Option Nat),
        ({ b1.modify l.owner (fun p => { p with backrow := p.backrow ++
            [{ card := l.card, setTurn := c.turn, faceUp := true, equipTo := eq, bond,
               since := b1.clock + 1 }] }) with clock := b1.clock + 1 } : Board).count = b.count + 1 := by
      intro eq bond
      have := b1.count_modify l.owner (fun p => { p with backrow := p.backrow ++
            [{ card := l.card, setTurn := c.turn, faceUp := true, equipTo := eq, bond,
               since := b1.clock + 1 }] })
      simp [Player.count] at this
      show (b1.modify _ _).count = _
      omega
    have hg := Board.count_toGrave b1 l
    simp only [linkCards, hm, Bool.false_eq_true, ite_false] at hg ⊢
    split
    · exact hkeep _ _
    · exact hkeep _ _
    · split
      · split
        · split
          · rw [hg, hA]
          · exact hkeep _ _
        · rw [hg, hA]
      · rw [hg, hA]
    · rw [hg, hA]
  · simp [linkCards, hm, hA]

theorem Board.count_resolveChain (c : Ctx) (ls : List ChainLink) (b : Board) (neg : Bool) :
    (resolveChain c b neg ls).count = b.count + nonMon ls := by
  induction ls generalizing b neg with
  | nil => simp [resolveChain, nonMon]
  | cons l rest ih =>
    simp only [resolveChain]
    rw [ih, nonMon_cons]
    split
    · rw [Board.count_toGrave]; omega
    · rw [Board.count_resolveLink]; omega

/-! ### 戦闘 -/

theorem Board.count_modify_damage (b : Board) (w : PlayerId) (n : Nat) :
    (b.modify w (·.damage n)).count = b.count := Board.count_modify_eq _ _ _ rfl

theorem Board.count_updMon_ite (b : Board) (w : PlayerId) (u : Nat) (p : Prop) [Decidable p]
    (pos : Position) (since : Nat) :
    (b.updMon w u fun x => if p then { x with pos, since } else x).count = b.count :=
  Board.count_updMon _ _ _ _ (fun x => by split <;> rfl)

theorem Board.count_performBattle (c : Ctx) (b : Board) : (performBattle c b).count = b.count := by
  unfold performBattle
  split
  · rfl
  · dsimp only
    split
    · rfl
    · split
      · rfl
      · split
        · split
          · exact Board.count_modify_damage _ _ _
          · rfl
        · split
          · rfl
          · simp only [apply_ite Board.count, Board.count_toGraveMon, Board.count_modify_damage,
              Board.count_updMon_ite, Board.count_log, Board.count_attack, ite_self]
            split <;> rfl

/-! ### 失敗しうる行動 -/

theorem pushLink_ok {s s' : ChainState} {b : Board} {l : ChainLink} (h : pushLink s b l = .ok s') :
    s'.board = b ∧ s'.chain = l :: s.chain := by
  unfold pushLink at h
  by_cases h1 : l.owner = s.priority
  · cases hc : s.chain with
    | nil =>
      simp [h1, hc, pure, Except.pure] at h
      subst h; simp
    | cons top rest =>
      by_cases h2 : 2 ≤ l.speed <;> by_cases h3 : top.speed ≤ l.speed <;>
        simp [h1, h2, h3, hc, bind, Except.bind, pure, Except.pure, throw, throwThe,
          MonadExceptOf.throw] at h
      subst h; simp
  · simp [h1, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h

theorem mkLink_mon {b : Board} {who : PlayerId} {card : Card} {eff : Effect} {speed : Nat}
    {args : Args} {shift : Option Nat} {l : ChainLink}
    (h : mkLink b who card eff speed args shift = .ok l) : l.mon = false := by
  unfold mkLink at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals first | (cases h; rfl) | simp_all

theorem ChainState.count_push {s s' : ChainState} {b : Board} {l : ChainLink} (h : pushLink s b l = .ok s') :
    s'.count = b.count + linkCards l + nonMon s.chain := by
  obtain ⟨hb, hc⟩ := pushLink_ok h
  simp only [ChainState.count, hb, hc, nonMon_cons]; omega

/-- 手札・魔法罠ゾーンから1枚取り出すと1枚減る -/
theorem Board.count_eraseHand {b : Board} {w : PlayerId} {i : Nat} {x : Card}
    (h : (b.get w).hand[i]? = some x) :
    (b.set w { lp := (b.get w).lp, deck := (b.get w).deck, extra := (b.get w).extra,
               hand := (b.get w).hand.eraseIdx i, monsters := (b.get w).monsters,
               backrow := (b.get w).backrow, grave := (b.get w).grave }).count + 1 = b.count := by
  have h1 := b.count_set w
    ({ lp := (b.get w).lp, deck := (b.get w).deck, extra := (b.get w).extra,
       hand := (b.get w).hand.eraseIdx i, monsters := (b.get w).monsters,
       backrow := (b.get w).backrow, grave := (b.get w).grave })
  have h2 := length_eraseIdx_of_getElem? h
  simp only [Player.count] at h1; omega

theorem Board.count_eraseBackrow {b : Board} {w : PlayerId} {i : Nat} {x : SetCard}
    (h : (b.get w).backrow[i]? = some x) :
    (b.set w { lp := (b.get w).lp, deck := (b.get w).deck, extra := (b.get w).extra,
               hand := (b.get w).hand, monsters := (b.get w).monsters,
               backrow := (b.get w).backrow.eraseIdx i, grave := (b.get w).grave }).count + 1 = b.count := by
  have h1 := b.count_set w
    ({ lp := (b.get w).lp, deck := (b.get w).deck, extra := (b.get w).extra,
       hand := (b.get w).hand, monsters := (b.get w).monsters,
       backrow := (b.get w).backrow.eraseIdx i, grave := (b.get w).grave })
  have h2 := length_eraseIdx_of_getElem? h
  simp only [Player.count] at h1; omega

theorem count_activateSpellAct {c : Ctx} {s s' : ChainState} {hd : Nat} {args : Args}
    (h : activateSpellAct c s hd args = .ok s') : s'.count = s.count := by
  unfold activateSpellAct at h
  simp only [bind, Except.bind] at h
  repeat' split at h
  all_goals try (simp_all [throw, throwThe, MonadExceptOf.throw]; done)
  have hm := mkLink_mon (by assumption : mkLink _ _ _ _ _ _ _ = .ok _)
  obtain ⟨_, hh⟩ : ∃ x, (s.board.get c.active).hand[hd]? = some x := ⟨_, by assumption⟩
  rw [ChainState.count_push h, linkCards, hm]
  have := Board.count_eraseHand hh
  simp only [ChainState.count]; simp; omega

theorem count_activateSetAct {c : Ctx} {s s' : ChainState} {who : PlayerId} {z : Nat} {args : Args}
    (h : activateSetAct c s who z args = .ok s') : s'.count = s.count := by
  unfold activateSetAct at h
  simp only [bind, Except.bind] at h
  repeat' split at h
  all_goals try (simp_all [throw, throwThe, MonadExceptOf.throw]; done)
  all_goals
    have hm := mkLink_mon (by assumption : mkLink _ _ _ _ _ _ _ = .ok _)
    obtain ⟨_, hz⟩ : ∃ x, (s.board.get who).backrow[z]? = some x := ⟨_, by assumption⟩
    rw [ChainState.count_push h, linkCards, hm, Board.count_modify_damage]
    have := Board.count_eraseBackrow hz
    simp only [ChainState.count]; simp; omega

theorem Board.count_setMonAt_same {b : Board} {w : PlayerId} {i : Nat} {m m' : FieldMonster}
    (h : (b.get w).monsters[i]? = some m) (ho : m'.overlays = m.overlays) :
    (b.setMonAt w i m').count = b.count := by
  have := Board.count_setMonAt b w i m m' h; rw [ho] at this; omega

theorem Board.getElem_setMonAt {b : Board} {w : PlayerId} {i : Nat} {m m' : FieldMonster}
    (h : (b.get w).monsters[i]? = some m) : ((b.setMonAt w i m').get w).monsters[i]? = some m' := by
  have hi : i < (b.get w).monsters.length := (List.getElem?_eq_some_iff.mp h).1
  cases w <;> simp_all [Board.setMonAt, Board.modify, Board.set, Board.get]

theorem Board.count_setMonAt_used {b : Board} {w : PlayerId} {i : Nat} {m : FieldMonster}
    (h : (b.get w).monsters[i]? = some m) : (b.setMonAt w i { m with effectUsed := true }).count = b.count :=
  Board.count_setMonAt_same h rfl

/-- X素材を取り除くコスト -/
theorem Board.count_detachCost {b : Board} {w : PlayerId} {i n : Nat} {m : FieldMonster}
    (h : (b.get w).monsters[i]? = some m) (hn : n ≤ m.overlays.length) :
    (((b.setMonAt w i { m with effectUsed := true }).setMonAt w i
        { m with effectUsed := true, overlays := m.overlays.drop n }).modify w
        (fun p => { p with grave := p.grave ++ m.overlays.take n })).count = b.count := by
  have h1 := Board.count_setMonAt_used h
  have h2 := Board.count_setMonAt (b.setMonAt w i { m with effectUsed := true }) w i
    { m with effectUsed := true } { m with effectUsed := true, overlays := m.overlays.drop n }
    (Board.getElem_setMonAt h)
  have h3 := ((b.setMonAt w i { m with effectUsed := true }).setMonAt w i
        { m with effectUsed := true, overlays := m.overlays.drop n }).count_modify w
        (fun p => { p with grave := p.grave ++ m.overlays.take n })
  simp only [Player.count, List.length_append, List.length_drop, List.length_take] at h2 h3
  omega


theorem count_activateMonsterAct {c : Ctx} {s s' : ChainState} {who : PlayerId} {z i : Nat} {args : Args}
    (h : activateMonsterAct c s who z i args = .ok s') : s'.count = s.count := by
  unfold activateMonsterAct at h
  simp only [bind, Except.bind] at h
  repeat' split at h
  all_goals try (simp_all [throw, throwThe, MonadExceptOf.throw]; done)
  all_goals
    rw [ChainState.count_push h]
    simp only [linkCards, ite_true, Nat.add_zero, ChainState.count, Nat.add_right_cancel_iff]
  all_goals
    rename_i hv
    simp only [pure, Except.pure, Except.ok.injEq] at hv
    subst hv
  · exact Board.count_setMonAt_used (by assumption)
  · rw [Board.count_toGraveMon]; exact Board.count_setMonAt_used (by assumption)
  · rw [Board.count_modify_damage]; exact Board.count_setMonAt_used (by assumption)
  · exact Board.count_detachCost (by assumption) (by assumption)
  · exact Board.count_setMonAt_used (by assumption)
  · rw [Board.count_toGraveMon]; exact Board.count_setMonAt_used (by assumption)
  · rw [Board.count_modify_damage]; exact Board.count_setMonAt_used (by assumption)
  · exact Board.count_detachCost (by assumption) (by assumption)

/-! ### 召喚・戦闘などの行動 -/

theorem Board.count_modify_eraseHand {b : Board} {w : PlayerId} {i : Nat} {x : Card}
    (h : (b.get w).hand[i]? = some x) :
    (b.modify w (fun p => { p with hand := p.hand.eraseIdx i })).count + 1 = b.count := by
  have h1 := b.count_modify w (fun p => { p with hand := p.hand.eraseIdx i })
  have h2 := length_eraseIdx_of_getElem? h
  simp only [Player.count] at h1; omega

theorem Board.count_modify_eraseExtra {b : Board} {w : PlayerId} {i : Nat} {x : Card}
    (h : (b.get w).extra[i]? = some x) :
    (b.modify w (fun p => { p with extra := p.extra.eraseIdx i })).count + 1 = b.count := by
  have h1 := b.count_modify w (fun p => { p with extra := p.extra.eraseIdx i })
  have h2 := length_eraseIdx_of_getElem? h
  simp only [Player.count] at h1; omega


theorem count_summonCore {c : Ctx} {b b' : Board} {hd : Nat} {ts : List Nat} {pos : Position}
    (h : summonCore c b hd ts pos = .ok b') : b'.count = b.count := by
  unfold summonCore at h
  simp only [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  repeat' split at h
  all_goals try (cases h; done)
  all_goals
    rename_i tms _ _ _ _
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    obtain ⟨_, hh⟩ : ∃ x, (b.get c.active).hand[hd]? = some x := ⟨_, by assumption⟩
    have hf := Board.frame_foldl_toGraveMon tms (·.uid) LeaveCause.sent b
    have hc := Board.count_foldl_toGraveMon' tms (·.uid) LeaveCause.sent b
    rw [← (hf c.active).2.2.2] at hh
    have := Board.count_modify_eraseHand hh
    rw [Board.count_ns, Board.count_place]; simp; omega

theorem monCount_eq (l : List FieldMonster) : monCount l = (l.flatMap (·.overlays)).length + l.length := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [monCount] at ih ⊢; omega

theorem Board.count_detachAllAux (ms : List FieldMonster) (acc : Board × List FieldMonster) :
    (Board.detachAllAux acc ms).1.count + monCount (Board.detachAllAux acc ms).2 =
      acc.1.count + monCount acc.2 := by
  induction ms generalizing acc with
  | nil => rfl
  | cons m ms ih =>
    simp only [Board.detachAllAux]
    rw [ih]
    split
    · rename_i b x hd
      have := Board.count_detach hd
      simp [monCount] at this ⊢; omega
    · rfl

theorem Board.frame_detachAllAux (ms : List FieldMonster) (acc : Board × List FieldMonster) :
    acc.1.Frame (Board.detachAllAux acc ms).1 := by
  induction ms generalizing acc with
  | nil => exact Board.Frame.refl _
  | cons m ms ih =>
    simp only [Board.detachAllAux]
    refine Board.Frame.trans ?_ (ih _)
    split
    · rename_i b x hd; exact Board.frame_detach hd
    · exact Board.Frame.refl _

theorem Board.count_extra_xyz' {b b1 : Board} {tms got : List FieldMonster} {w : PlayerId} {ei : Nat}
    {x : Card} {em : MonsterCard} {pos : Position} {t : Nat} {emz : Bool} {ev : Option Event}
    (hd : b.detachAll tms = (b1, got)) (hx : (b.get w).extra[ei]? = some x) :
    (((b1.modify w fun p => { p with grave := p.grave ++ got.flatMap (·.overlays) }).modify w
        fun p => { p with extra := p.extra.eraseIdx ei }).place w em pos t emz ev
        (got.map fun m => Card.monster m.card)).count = b.count := by
  have h1 := Board.count_detachAllAux tms (b, [])
  have hf := Board.frame_detachAllAux tms (b, [])
  simp only [Board.detachAll] at hd
  rw [hd] at h1 hf
  have h2 := b1.count_modify w (fun p => { p with grave := p.grave ++ got.flatMap (·.overlays) })
  have hx' : ((b1.modify w fun p => { p with grave := p.grave ++ got.flatMap (·.overlays) }).get
      w).extra[ei]? = some x := by
    rw [Board.get_modify_same]; show (b1.get w).extra[ei]? = _; rw [(hf w).2.2.1]; exact hx
  have h3 := Board.count_modify_eraseExtra hx'
  have h4 := monCount_eq got
  rw [Board.count_place]
  simp only [Player.count, List.length_append] at h2
  have h0 : monCount [] = 0 := rfl
  simp only [h0, Nat.add_zero] at h1
  simp only [List.length_map]
  omega

theorem Board.count_extra_xyz {b : Board} {tms : List FieldMonster} {w : PlayerId} {ei : Nat}
    {x : Card} {em : MonsterCard} {pos : Position} {t : Nat} {emz : Bool} {ev : Option Event}
    (hx : (b.get w).extra[ei]? = some x) :
    ((((b.detachAll tms).1.modify w fun p => { p with grave := p.grave ++ (b.detachAll tms).2.flatMap (·.overlays) }).modify w
        fun p => { p with extra := p.extra.eraseIdx ei }).place w em pos t emz ev
        ((b.detachAll tms).2.map fun m => Card.monster m.card)).count = b.count :=
  Board.count_extra_xyz' rfl hx

theorem Board.count_extra_other {b : Board} {tms : List FieldMonster} {w : PlayerId} {ei : Nat}
    {x : Card} {em : MonsterCard} {pos : Position} {t : Nat} {emz : Bool} {ev : Option Event}
    (hx : (b.get w).extra[ei]? = some x) :
    (((tms.foldl (fun b m => b.toGraveMon m.uid) b).modify w
        fun p => { p with extra := p.extra.eraseIdx ei }).place w em pos t emz ev []).count = b.count := by
  have hf := Board.frame_foldl_toGraveMon tms (·.uid) LeaveCause.sent b
  have hc := Board.count_foldl_toGraveMon' tms (·.uid) LeaveCause.sent b
  rw [← (hf w).2.2.1] at hx
  have := Board.count_modify_eraseExtra hx
  rw [Board.count_place]; simp; omega

theorem count_extraSummonAct {c : Ctx} {b b' : Board} {ei : Nat} {ms : List Nat}
    (h : extraSummonAct c b ei ms = .ok b') : b'.count = b.count := by
  unfold extraSummonAct at h
  simp only [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  repeat' split at h
  all_goals try (cases h; done)
  all_goals simp only [pure, Except.pure, Except.ok.injEq] at h
  all_goals subst h
  · exact Board.count_extra_xyz (by assumption)
  · exact Board.count_extra_other (by assumption)
  · exact Board.count_extra_xyz (by assumption)
  · exact Board.count_extra_other (by assumption)
  · exact Board.count_extra_xyz (by assumption)
  · exact Board.count_extra_other (by assumption)
  · exact Board.count_extra_xyz (by assumption)
  · exact Board.count_extra_other (by assumption)

theorem Board.count_setST {b : Board} {w : PlayerId} {i t : Nat} {x : Card}
    (h : (b.get w).hand[i]? = some x) :
    (b.set w { lp := (b.get w).lp, deck := (b.get w).deck, extra := (b.get w).extra,
               hand := (b.get w).hand.eraseIdx i, monsters := (b.get w).monsters,
               backrow := (b.get w).backrow ++ [{ card := x, setTurn := t }],
               grave := (b.get w).grave }).count = b.count := by
  have h1 := b.count_set w
    ({ lp := (b.get w).lp, deck := (b.get w).deck, extra := (b.get w).extra,
       hand := (b.get w).hand.eraseIdx i, monsters := (b.get w).monsters,
       backrow := (b.get w).backrow ++ [{ card := x, setTurn := t }],
       grave := (b.get w).grave })
  have h2 := length_eraseIdx_of_getElem? h
  simp only [Player.count, List.length_append, List.length_cons, List.length_nil] at h1
  omega

theorem Board.count_discard {b : Board} {w : PlayerId} {i : Nat} {x : Card}
    (h : (b.get w).hand[i]? = some x) :
    (b.set w { lp := (b.get w).lp, deck := (b.get w).deck, extra := (b.get w).extra,
               hand := (b.get w).hand.eraseIdx i, monsters := (b.get w).monsters,
               backrow := (b.get w).backrow, grave := (b.get w).grave ++ [x] }).count = b.count := by
  have h1 := b.count_set w
    ({ lp := (b.get w).lp, deck := (b.get w).deck, extra := (b.get w).extra,
       hand := (b.get w).hand.eraseIdx i, monsters := (b.get w).monsters,
       backrow := (b.get w).backrow, grave := (b.get w).grave ++ [x] })
  have h2 := length_eraseIdx_of_getElem? h
  simp only [Player.count, List.length_append, List.length_cons, List.length_nil] at h1
  omega

theorem count_declareAttack {c : Ctx} {b b' : Board} {ai : Nat} {tg : Option Nat}
    (h : declareAttack c b ai tg = .ok b') : b'.count = b.count := by
  unfold declareAttack at h
  simp only [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  repeat' split at h
  all_goals try (cases h; done)
  all_goals simp only [pure, Except.pure, Except.ok.injEq] at h
  all_goals subst h
  all_goals exact Board.count_updMon _ _ _ _ (fun _ => rfl)

theorem count_changePositionAct {c : Ctx} {b b' : Board} {i : Nat}
    (h : changePositionAct c b i = .ok b') : b'.count = b.count := by
  unfold changePositionAct at h
  simp only [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  repeat' split at h
  all_goals try (cases h; done)
  all_goals simp only [pure, Except.pure, Except.ok.injEq] at h
  all_goals subst h
  all_goals exact Board.count_updMon _ _ _ _ (fun _ => rfl)

theorem count_flipSummonAct {c : Ctx} {b b' : Board} {i : Nat}
    (h : flipSummonAct c b i = .ok b') : b'.count = b.count := by
  unfold flipSummonAct at h
  simp only [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  repeat' split at h
  all_goals try (cases h; done)
  all_goals simp only [pure, Except.pure, Except.ok.injEq] at h
  all_goals subst h
  all_goals exact Board.count_updMon _ _ _ _ (fun _ => rfl)

theorem count_setSpellTrapAct {c : Ctx} {b b' : Board} {hd : Nat}
    (h : setSpellTrapAct c b hd = .ok b') : b'.count = b.count := by
  unfold setSpellTrapAct at h
  simp only [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  repeat' split at h
  all_goals try (cases h; done)
  all_goals simp only [pure, Except.pure, Except.ok.injEq] at h
  all_goals subst h
  all_goals exact Board.count_setST (by assumption)

theorem count_discardAct {c : Ctx} {b b' : Board} {hd : Nat}
    (h : discardAct c b hd = .ok b') : b'.count = b.count := by
  unfold discardAct at h
  simp only [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  repeat' split at h
  all_goals try (cases h; done)
  all_goals simp only [pure, Except.pure, Except.ok.injEq] at h
  all_goals subst h
  all_goals exact Board.count_discard (by assumption)


theorem count_boardAct {c : Ctx} {b b' : Board} {a : Action} (h : boardAct c b a = .ok b') :
    b'.count = b.count := by
  cases a <;> simp only [boardAct] at h
  case normalSummon => exact count_summonCore h
  case normalSet => exact count_summonCore h
  case flipSummon => exact count_flipSummonAct h
  case changePosition => exact count_changePositionAct h
  case extraSummon => exact count_extraSummonAct h
  case setSpellTrap => exact count_setSpellTrapAct h
  case attack => exact count_declareAttack h
  case discard => exact count_discardAct h
  all_goals cases h

theorem count_passAct (c : Ctx) (s : ChainState) : (passAct c s).count = s.count := by
  unfold passAct
  split
  · split
    · rename_i he
      simp only [List.isEmpty_iff] at he
      simp [ChainState.count, Board.count_performBattle, he, nonMon]
    · simp [ChainState.count, Board.count_resolveChain, nonMon]
  · rfl

theorem Except.map_ok {α β : Type} {f : α → β} {x : Except String α} {y : β}
    (h : Except.map f x = .ok y) : ∃ a, x = .ok a ∧ f a = y := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, by simpa [Except.map] using h⟩

theorem count_act {c : Ctx} {s s' : ChainState} {a : Action} (h : act c s a = .ok s') :
    s'.count = s.count := by
  cases a <;> simp only [act] at h
  case pass => simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; exact count_passAct c s
  case activateSpell => exact count_activateSpellAct h
  case activateSet => exact count_activateSetAct h
  case activateMonster => exact count_activateMonsterAct h
  all_goals try simp only [throw, throwThe, MonadExceptOf.throw] at h
  all_goals repeat' split at h
  all_goals try (cases h; done)
  all_goals
    obtain ⟨b, hb, rfl⟩ := Except.map_ok h
    simp only [ChainState.count]
    rw [count_boardAct hb]

theorem triggeredLinks_mon {h : Happened} {l : ChainLink} (hl : l ∈ triggeredLinks h) : l.mon = true := by
  unfold triggeredLinks at hl
  simp only [List.mem_filterMap] at hl
  obtain ⟨e, _, he⟩ := hl
  split at he
  · split at he
    · simp at he; subst he; rfl
    · simp at he
  · simp at he

theorem nonMon_all_mon {ls : List ChainLink} (h : ∀ l ∈ ls, l.mon = true) : nonMon ls = 0 := by
  unfold nonMon
  simp only [List.length_eq_zero_iff, List.filter_eq_nil_iff, Bool.not_eq_true']
  intro l hl; simp [h l hl]

theorem count_processTriggers (c : Ctx) (s : ChainState) : (processTriggers c s).count = s.count := by
  unfold processTriggers
  split
  · rfl
  · rename_i hc
    simp only [Bool.not_eq_true', List.isEmpty_eq_false_iff, ne_eq, Decidable.not_not] at hc
    dsimp only
    split
    · rfl
    · simp only [ChainState.count, hc]
      rw [nonMon_all_mon, nonMon_all_mon (ls := [])]
      · rfl
      · simp
      · intro l hl
        simp only [List.mem_reverse, List.mem_append, List.mem_filter, List.mem_flatMap] at hl
        rcases hl with ⟨⟨h, _, hl⟩, _⟩ | ⟨⟨h, _, hl⟩, _⟩ <;> exact triggeredLinks_mon hl

theorem Player.count_resetMonsters (p : Player) : p.resetMonsters.count = p.count := by
  simp only [Player.resetMonsters, Player.count]
  rw [monCount_map (f := fun m => { m with attacked := false, posChanged := false, effectUsed := false })
    (fun _ => rfl)]

theorem count_nextPhase {g g' : Game} (h : nextPhase g = .ok g') : g'.count = g.count := by
  unfold nextPhase at h
  split at h
  all_goals try (simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; rfl)
  · split at h <;> (simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; rfl)
  · split at h
    · cases h
    · dsimp only at h
      split at h
      · simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
        simp only [Game.count, Board.count_modify_eq _ _ _ (Player.count_resetMonsters _)]
        rfl
      · rename_i p hp
        simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
        simp only [Game.count]
        rw [Board.count_set_eq _ _ _ (Player.count_drawOne hp),
          Board.count_modify_eq _ _ _ (Player.count_resetMonsters _),
          Board.count_modify_eq _ _ _ (Player.count_resetMonsters _)]
        rfl

/-- **1手進めてもカードの総数は変わらない** -/
theorem step_count {g g' : Game} {a : Action} (h : step g a = .ok g') : g'.count = g.count := by
  unfold step at h
  split at h
  · cases h
  · split at h
    · split at h
      · exact count_nextPhase h
      · cases h
    · cases ha : act g.ctx g.cs a <;> simp only [ha, Except.map] at h
      · cases h
      · rename_i s0
        simp only [Except.ok.injEq] at h; subst h
        have h1 := count_act ha
        have h2 := count_processTriggers g.ctx s0
        simp only [Game.count, checkResult, Game.setCs, ChainState.count, Game.cs] at h1 h2 ⊢
        omega

/-- **合法な手順を何手進めても、カードの総数は最初と同じ** -/
theorem play_count {g g' : Game} {as : List Action} (h : play g as = .ok g') : g'.count = g.count := by
  induction as generalizing g with
  | nil => simp [play, List.foldlM, pure, Except.pure] at h; subst h; rfl
  | cons a as ih =>
    simp only [play, List.foldlM, bind, Except.bind] at h
    cases hs : step g a <;> simp only [hs] at h
    · cases h
    · rename_i g1; rw [ih h, step_count hs]

end YGO

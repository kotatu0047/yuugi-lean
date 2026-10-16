import YuugiLean.YuGiOh

/-!
# 不変条件

`step` で1手進めても保たれる性質を証明する。

* カードの総数は変わらない（`step_count`、`play_count`）
* フィールドのモンスターの uid は重複しない（`step_uidOK`、`reachable_uidOK`）
* ゾーンの上限を超えない：メインモンスターゾーン5・エクストラモンスターゾーン1・
  魔法罠ゾーン（チェーン上の魔法・罠を含む）5（`step_zoneOK`、`reachable_zoneOK`）
* どちらかの LP が 0 なら決着している（`reachable_lp_zero_decided`）
* 永続効果の有効・無効の判定（`settle`）について
  * 判定で変わるのは有効・無効と適用の時刻だけ（`settle_keys`）
  * 判定が止まった状態（決まったか、プレイヤーの選択待ち）では
    * 有効なカード同士は互いに無効にしない（`settled_consistent`）
    * 選択待ちでなければ、無効なカードには、それを無効にする有効なカードがある（`negated_has_reason`）
    * 選択待ちでなければ、どのカードにも無効にされないカードは有効（`unbeaten_effective`）
  * 判定が必ず決まることは `Settle.lean`（`settle_settled`、`reachable_settled`）
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

theorem Board.count_destroyBackrow (b : Board) (w : PlayerId) (i : Nat) :
    (b.destroyBackrow w i).count = b.count := by
  unfold Board.destroyBackrow
  split
  · rfl
  · rename_i s hs
    have h0 : (b.modify w fun p => { p with backrow := p.backrow.eraseIdx i, grave := p.grave ++ [s.card] }).count
        = b.count := by
      apply Board.count_modify_eq
      have := length_eraseIdx_of_getElem? hs
      simp only [Player.count, List.length_append, List.length_cons, List.length_nil] at this ⊢; omega
    simp only
    split
    · split
      · exact h0
      · rw [Board.count_toGraveMon]; exact h0
    · exact h0

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
  case destroySpellTrap =>
    split
    · split
      · exact Board.count_destroyBackrow _ _ _
      · rfl
    · rfl
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
               since := b1.clock + 1, id := b1.clock + 1 }] }) with clock := b1.clock + 1 } : Board).count = b.count + 1 := by
      intro eq bond
      have := b1.count_modify l.owner (fun p => { p with backrow := p.backrow ++
            [{ card := l.card, setTurn := c.turn, faceUp := true, equipTo := eq, bond,
               since := b1.clock + 1, id := b1.clock + 1 }] })
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

theorem Board.count_setST {b : Board} {w : PlayerId} {i : Nat} {x : Card} {y : SetCard}
    (h : (b.get w).hand[i]? = some x) :
    (b.set w { lp := (b.get w).lp, deck := (b.get w).deck, extra := (b.get w).extra,
               hand := (b.get w).hand.eraseIdx i, monsters := (b.get w).monsters,
               backrow := (b.get w).backrow ++ [y],
               grave := (b.get w).grave }).count = b.count := by
  have h1 := b.count_set w
    ({ lp := (b.get w).lp, deck := (b.get w).deck, extra := (b.get w).extra,
       hand := (b.get w).hand.eraseIdx i, monsters := (b.get w).monsters,
       backrow := (b.get w).backrow ++ [y],
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
  all_goals exact (Board.count_clock _ _).trans (Board.count_setST (by assumption))

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

/-! ### 永続効果の判定結果の書き込み（`commitAuras`）はカードを動かさない -/

@[simp] theorem FieldMonster.commitAura_uid (r : List AuraSrc) (m : FieldMonster) :
    (m.commitAura r).uid = m.uid := by unfold FieldMonster.commitAura; split <;> rfl
@[simp] theorem FieldMonster.commitAura_emz (r : List AuraSrc) (m : FieldMonster) :
    (m.commitAura r).emz = m.emz := by unfold FieldMonster.commitAura; split <;> rfl
@[simp] theorem FieldMonster.commitAura_overlays (r : List AuraSrc) (m : FieldMonster) :
    (m.commitAura r).overlays = m.overlays := by unfold FieldMonster.commitAura; split <;> rfl

theorem Player.count_commitAuras (p : Player) (w : PlayerId) (r : List AuraSrc) :
    (p.commitAuras w r).count = p.count := by
  simp only [Player.commitAuras, Player.count, List.length_mapIdx]
  rw [monCount_map (FieldMonster.commitAura_overlays r)]

theorem Board.count_commitAuras (b : Board) : b.commitAuras.count = b.count := by
  simp only [Board.commitAuras, Board.count, Player.count_commitAuras]

/-- 有効に戻すカードを選ぶと、判定結果を書き込んだ盤面になる -/
theorem Board.chooseAura_ok {b b' : Board} {i : Nat} (h : b.chooseAura i = .ok b') :
    ∃ r t, b' = { b with p1 := b.p1.commitAuras .one r, p2 := b.p2.commitAuras .two r, clock := t } := by
  unfold Board.chooseAura at h
  repeat' split at h
  all_goals try (cases h; done)
  simp only [pure, Except.pure, Except.ok.injEq] at h
  exact ⟨_, _, h.symm⟩

theorem Board.count_chooseAura {b b' : Board} {i : Nat} (h : b.chooseAura i = .ok b') : b'.count = b.count := by
  obtain ⟨r, t, rfl⟩ := Board.chooseAura_ok h
  simp only [Board.count, Player.count_commitAuras]

/-- **1手進めてもカードの総数は変わらない** -/
theorem step_count {g g' : Game} {a : Action} (h : step g a = .ok g') : g'.count = g.count := by
  unfold step at h
  split at h
  · cases h
  split at h
  · obtain ⟨i, b, -, hb, rfl⟩ := chooseStep_ok h
    simp only [Game.count, checkResult, Board.count_commitAuras, Board.count_chooseAura hb]
  · split at h
    · split at h
      · exact count_nextPhase h
      · cases h
    · cases ha : act g.ctx g.cs a <;> simp only [ha, Except.map] at h
      · cases h
      · rename_i s0
        simp only [Except.ok.injEq] at h; subst h
        have h1 := count_act ha
        have h2 := count_processTriggers g.ctx { s0 with board := s0.board.commitAuras }
        have h3 := Board.count_commitAuras s0.board
        simp only [Game.count, checkResult, Game.setCs, ChainState.count, Game.cs] at h1 h2 h3 ⊢
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

namespace YGO

/-! ## uid が重複しないこと -/

def Board.uidsOf (b : Board) (v : PlayerId) : List Nat := (b.get v).monsters.map (·.uid)

def Board.uids (b : Board) : List Nat := b.uidsOf .one ++ b.uidsOf .two

/-- フィールドのモンスターの uid は互いに異なり、すべて `nextUid` 未満 -/
def Board.UidOK (b : Board) : Prop := b.uids.Nodup ∧ ∀ u ∈ b.uids, u < b.nextUid

/-- モンスターが減るか変わらないだけ（uid は増えない） -/
def Board.Shrink (b b' : Board) : Prop :=
  (∀ v, (b'.uidsOf v).Sublist (b.uidsOf v)) ∧ b.nextUid ≤ b'.nextUid

theorem Board.Shrink.refl (b : Board) : b.Shrink b := ⟨fun _ => List.Sublist.refl _, Nat.le_refl _⟩

theorem Board.Shrink.trans {b b' b'' : Board} (h1 : b.Shrink b') (h2 : b'.Shrink b'') : b.Shrink b'' :=
  ⟨fun v => (h2.1 v).trans (h1.1 v), Nat.le_trans h1.2 h2.2⟩

theorem Board.UidOK.shrink {b b' : Board} (h : b.UidOK) (hs : b.Shrink b') : b'.UidOK := by
  have hsub : b'.uids.Sublist b.uids := (hs.1 .one).append (hs.1 .two)
  exact ⟨h.1.sublist hsub, fun u hu => Nat.lt_of_lt_of_le (h.2 u (hsub.subset hu)) hs.2⟩

theorem Board.Shrink.same {b b' : Board} (h1 : b'.p1.monsters = b.p1.monsters)
    (h2 : b'.p2.monsters = b.p2.monsters) (hn : b.nextUid ≤ b'.nextUid) : b.Shrink b' := by
  refine ⟨fun v => ?_, hn⟩
  cases v <;> simp [Board.uidsOf, Board.get, h1, h2]

theorem Board.shrink_modify (b : Board) (w : PlayerId) (f : Player → Player)
    (hf : ((f (b.get w)).monsters.map (·.uid)).Sublist ((b.get w).monsters.map (·.uid))) :
    b.Shrink (b.modify w f) := by
  refine ⟨fun v => ?_, by cases w <;> exact Nat.le_refl _⟩
  by_cases hv : v = w
  · subst hv; simp only [Board.uidsOf, Board.get_modify_same]; exact hf
  · simp only [Board.uidsOf, Board.get_modify_other _ _ _ _ hv]; exact List.Sublist.refl _

theorem Board.shrink_modify_eq (b : Board) (w : PlayerId) (f : Player → Player)
    (hf : (f (b.get w)).monsters = (b.get w).monsters) : b.Shrink (b.modify w f) :=
  b.shrink_modify w f (by rw [hf]; exact List.Sublist.refl _)

theorem Board.shrink_set (b : Board) (w : PlayerId) (p : Player) (hp : p.monsters = (b.get w).monsters) :
    b.Shrink (b.set w p) := b.shrink_modify_eq w (fun _ => p) hp

theorem Board.uidOK_place {b : Board} (h : b.UidOK) (w : PlayerId) (c : MonsterCard) (pos : Position)
    (t : Nat) (emz : Bool) (ev : Option Event) (ov : List Card) :
    (b.place w c pos t emz ev ov).UidOK := by
  obtain ⟨hn, hb⟩ := h
  have hfresh : b.nextUid ∉ b.uids := fun hm => Nat.lt_irrefl _ (hb _ hm)
  cases w <;> simp only [Board.UidOK, Board.uids, Board.uidsOf, Board.place, Board.modify, Board.set,
    Board.get, List.map_append, List.map_cons, List.map_nil] at hn hb hfresh ⊢
  · constructor
    · rw [List.append_assoc]
      refine List.nodup_append.mpr ⟨hn.sublist (List.sublist_append_left _ _), ?_, ?_⟩
      · refine List.nodup_append.mpr ⟨(by simp : [b.nextUid].Nodup), hn.sublist (List.sublist_append_right _ _), ?_⟩
        intro a ha b' hb' hab; simp at ha; subst ha; subst hab; exact hfresh (List.mem_append_right _ hb')
      · intro a ha b' hb' hab
        simp only [List.mem_append, List.mem_singleton] at hb'
        rcases hb' with rfl | hb'
        · subst hab; exact hfresh (List.mem_append_left _ ha)
        · exact (List.nodup_append.mp hn).2.2 a ha b' hb' hab
    · intro u hu
      simp only [List.mem_append, List.mem_singleton] at hu
      rcases hu with (hu | rfl) | hu
      · exact Nat.lt_succ_of_lt (hb u (List.mem_append_left _ hu))
      · exact Nat.lt_succ_self _
      · exact Nat.lt_succ_of_lt (hb u (List.mem_append_right _ hu))
  · constructor
    · refine List.nodup_append.mpr ⟨hn.sublist (List.sublist_append_left _ _),
        List.nodup_append.mpr ⟨hn.sublist (List.sublist_append_right _ _), (by simp : [b.nextUid].Nodup), ?_⟩, ?_⟩
      · intro a ha b' hb' hab; simp at hb'; subst hb'; subst hab; exact hfresh (List.mem_append_right _ ha)
      · intro a ha b' hb' hab
        simp only [List.mem_append, List.mem_singleton] at hb'
        rcases hb' with hb' | rfl
        · exact (List.nodup_append.mp hn).2.2 a ha b' hb' hab
        · subst hab; exact hfresh (List.mem_append_left _ ha)
    · intro u hu
      simp only [List.mem_append, List.mem_singleton] at hu
      rcases hu with hu | hu | rfl
      · exact Nat.lt_succ_of_lt (hb u (List.mem_append_left _ hu))
      · exact Nat.lt_succ_of_lt (hb u (List.mem_append_right _ hu))
      · exact Nat.lt_succ_self _

theorem Board.Shrink.with {b b' : Board} (h1 : b'.p1 = b.p1) (h2 : b'.p2 = b.p2) (hn : b'.nextUid = b.nextUid) :
    b.Shrink b' := Board.Shrink.same (by rw [h1]) (by rw [h2]) (Nat.le_of_eq hn.symm)

theorem Board.shrink_detach {b b' : Board} {u : Nat} {w : PlayerId} {m : FieldMonster}
    (h : b.detach u = some (b', w, m)) : b.Shrink b' := by
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
      obtain ⟨rfl, rfl, rfl⟩ := h
      refine ((b.shrink_modify w0 _ ?_).trans (Board.shrink_modify_eq _ _ _ (by rfl))).trans
        (Board.shrink_modify_eq _ _ _ (by rfl))
      exact (List.eraseIdx_sublist _ _).map _

theorem Board.shrink_toGraveMon (b : Board) (u : Nat) (cause : LeaveCause) :
    b.Shrink (b.toGraveMon u cause) := by
  unfold Board.toGraveMon
  split
  · exact Board.Shrink.refl _
  · rename_i b' w m hd
    refine (Board.shrink_detach hd).trans ((b'.shrink_modify_eq w
      (fun p => { p with grave := p.grave ++ m.overlays ++ [.monster m.card] }) rfl).trans ?_)
    by_cases hc : (cause == LeaveCause.sent) = true
    · simp only [hc, ite_true]; exact Board.Shrink.with rfl rfl rfl
    · simp only [hc, Bool.false_eq_true, ite_false]
      refine ⟨fun v => ?_, ?_⟩
      · cases v <;> cases w <;> simp [Board.uidsOf, Board.modify, Board.set, Board.get] <;>
          exact List.Sublist.refl _
      · cases w <;> simp [Board.modify, Board.set]

theorem Board.shrink_foldl_toGraveMon {α : Type} (xs : List α) (f : α → Nat) (cause : LeaveCause)
    (b : Board) : b.Shrink (xs.foldl (fun b x => b.toGraveMon (f x) cause) b) := by
  induction xs generalizing b with
  | nil => exact Board.Shrink.refl _
  | cons x xs ih => exact (Board.shrink_toGraveMon _ _ _).trans (ih _)

theorem Board.shrink_foldl_toGraveMonN (us : List Nat) (cause : LeaveCause) (b : Board) :
    b.Shrink (us.foldl (fun b u => b.toGraveMon u cause) b) :=
  Board.shrink_foldl_toGraveMon us id cause b

theorem Board.shrink_destroyAllOf (b : Board) (w : PlayerId) : b.Shrink (b.destroyAllOf w) :=
  Board.shrink_foldl_toGraveMon _ _ _ _

theorem Board.shrink_destroyBackrow (b : Board) (w : PlayerId) (i : Nat) : b.Shrink (b.destroyBackrow w i) := by
  unfold Board.destroyBackrow
  split
  · exact Board.Shrink.refl _
  · rename_i s _
    have h0 := Board.shrink_modify_eq b w
      (fun p => { p with backrow := p.backrow.eraseIdx i, grave := p.grave ++ [s.card] }) rfl
    simp only
    split
    · split
      · exact h0
      · exact h0.trans (Board.shrink_toGraveMon _ _ _)
    · exact h0

theorem Board.shrink_destroyAllBackrow (b : Board) (ws : List PlayerId) : b.Shrink (b.destroyAllBackrow ws) := by
  unfold Board.destroyAllBackrow
  simp only
  refine Board.Shrink.trans ?_ (Board.shrink_foldl_toGraveMonN _ _ _)
  generalize b = b0
  induction ws generalizing b0 with
  | nil => exact Board.Shrink.refl _
  | cons w ws ih => exact (Board.shrink_modify_eq _ _ _ (by rfl)).trans (ih _)

theorem Board.shrink_updMon (b : Board) (w : PlayerId) (u : Nat) (f : FieldMonster → FieldMonster)
    (hf : ∀ x, (f x).uid = x.uid) : b.Shrink (b.updMon w u f) := by
  unfold Board.updMon
  apply Board.shrink_modify
  simp only [List.map_map]
  rw [show ((·.uid) ∘ fun m : FieldMonster => if m.uid = u then f m else m) = (·.uid) from by
    funext x; simp only [Function.comp]; split <;> simp [hf]]
  exact List.Sublist.refl _

theorem Board.shrink_setMonAt {b : Board} {w : PlayerId} {i : Nat} {m m' : FieldMonster}
    (h : (b.get w).monsters[i]? = some m) (hu : m'.uid = m.uid) : b.Shrink (b.setMonAt w i m') := by
  unfold Board.setMonAt
  apply Board.shrink_modify
  have : ((b.get w).monsters.set i m').map (·.uid) = (b.get w).monsters.map (·.uid) := by
    rw [List.map_set]
    have hi := List.getElem?_eq_some_iff.mp h
    rw [hu]
    apply List.ext_getElem? ; intro j
    by_cases hj : j = i
    · subst hj; simp [hi.1, ← hi.2]
    · simp [Ne.symm hj]
  simp only; rw [this]; exact List.Sublist.refl _

theorem Board.shrink_damage (b : Board) (w : PlayerId) (n : Nat) : b.Shrink (b.modify w (·.damage n)) :=
  Board.shrink_modify_eq _ _ _ rfl

theorem Player.monsters_drawN {n : Nat} {p p' : Player} (h : p.drawN n = some p') : p'.monsters = p.monsters := by
  induction n generalizing p with
  | zero => simp [Player.drawN] at h; subst h; rfl
  | succ n ih =>
    simp only [Player.drawN, Option.bind_eq_some_iff] at h
    obtain ⟨q, hq, hr⟩ := h
    rw [ih hr]
    unfold Player.drawOne at hq; split at hq <;> simp at hq; subst hq; rfl

theorem Player.monsters_drawOne {p p' : Player} (h : p.drawOne = some p') : p'.monsters = p.monsters :=
  Player.monsters_drawN (n := 1) (by simp [Player.drawN, h])

/-- **効果を適用しても uid は重複しない** -/
theorem Board.uidOK_applyEffect {c : Ctx} {l : ChainLink} {b : Board} (h : b.UidOK) :
    (applyEffect c l b).UidOK := by
  unfold applyEffect
  cases he : l.eff <;> simp only
  case noop => exact h
  case burn => exact h.shrink (Board.shrink_damage _ _ _)
  case heal => exact h.shrink (Board.shrink_modify_eq _ _ _ (by rfl))
  case draw n =>
    split
    · exact h
    · rename_i p hp; exact h.shrink (Board.shrink_set _ _ _ (Player.monsters_drawN hp))
  case destroyOppMonsters => exact h.shrink (Board.shrink_destroyAllOf _ _)
  case destroyAllMonsters => exact h.shrink ((Board.shrink_destroyAllOf _ _).trans (Board.shrink_destroyAllOf _ _))
  case burnPerOppMonster => exact h.shrink (Board.shrink_damage _ _ _)
  case negate n =>
    split
    · exact h
    · rename_i p hp; exact h.shrink (Board.shrink_set _ _ _ (Player.monsters_drawN hp))
  case destroyTarget => exact h.shrink (Board.shrink_foldl_toGraveMonN _ _ _)
  case revive own =>
    split
    · exact h
    · exact Board.uidOK_place (h.shrink (Board.shrink_modify_eq _ _ _ (by rfl))) _ _ _ _ _ _ _
  case fusionSummon =>
    split
    · exact h
    · have h1 := h.shrink ((Board.shrink_modify_eq b l.owner (fun p =>
          let r := removeIdxs p.hand (l.handMats.map (·.1))
          { p with hand := r.1, grave := p.grave ++ r.2 }) rfl).trans
        (Board.shrink_foldl_toGraveMonN l.fieldMats LeaveCause.sent _))
      split
      · exact Board.uidOK_place (h1.shrink (Board.shrink_modify_eq _ _ _ (by rfl))) _ _ _ _ _ _ _
      · exact h1
  case destroyAttacker =>
    split
    · exact (h.shrink (Board.shrink_toGraveMon _ _ _)).shrink (Board.Shrink.with rfl rfl rfl)
    · exact h
  case negateAttack => exact h.shrink (Board.Shrink.with rfl rfl rfl)
  case destroyOppSpellTraps => exact h.shrink (Board.shrink_destroyAllBackrow _ _)
  case destroyAllSpellTraps => exact h.shrink (Board.shrink_destroyAllBackrow _ _)
  case destroySpellTrap =>
    split
    · split
      · exact h.shrink (Board.shrink_destroyBackrow _ _ _)
      · exact h
    · exact h
  case millOpp => exact h.shrink (Board.shrink_modify_eq _ _ _ (by rfl))
  case recruit =>
    split
    · split
      · split
        · exact Board.uidOK_place (h.shrink (Board.shrink_set _ _ _ (by rfl))) _ _ _ _ _ _ _
        · exact h
      · exact h
    · exact h
  case searchMaxDef =>
    split
    · split
      · exact h.shrink (Board.shrink_set _ _ _ (by rfl))
      · exact h
    · exact h

theorem Board.UidOK.same {b b' : Board} (h : b.UidOK) (h1 : b'.p1 = b.p1) (h2 : b'.p2 = b.p2)
    (hn : b'.nextUid = b.nextUid) : b'.UidOK := h.shrink (Board.Shrink.with h1 h2 hn)

theorem Board.UidOK.modify_eq {b : Board} {w : PlayerId} {f : Player → Player} (h : b.UidOK)
    (hf : (f (b.get w)).monsters = (b.get w).monsters) : (b.modify w f).UidOK :=
  h.shrink (b.shrink_modify_eq w f hf)

theorem Board.UidOK.set_eq {b : Board} {w : PlayerId} {p : Player} (h : b.UidOK)
    (hp : p.monsters = (b.get w).monsters) : (b.set w p).UidOK :=
  h.shrink (b.shrink_set w p hp)

theorem Board.UidOK.toGraveMon {b : Board} (h : b.UidOK) (u : Nat) (c : LeaveCause) :
    (b.toGraveMon u c).UidOK := h.shrink (Board.shrink_toGraveMon _ _ _)

theorem Board.UidOK.updMon {b : Board} (h : b.UidOK) (w : PlayerId) (u : Nat) (f : FieldMonster → FieldMonster)
    (hf : ∀ x, (f x).uid = x.uid) : (b.updMon w u f).UidOK := h.shrink (Board.shrink_updMon _ _ _ _ hf)

theorem Board.uidOK_resolveLink {c : Ctx} {b : Board} {l : ChainLink} (h : b.UidOK) :
    (resolveLink c b l).UidOK := by
  have hA : (if b.effectNegated l then b else applyEffect c l b).UidOK := by
    split
    · exact h
    · exact Board.uidOK_applyEffect h
  unfold resolveLink
  simp only
  generalize (if b.effectNegated l then b else applyEffect c l b) = b1 at hA
  split
  · exact hA
  · have hg : (toGrave b1 l).UidOK := by
      unfold toGrave; split
      · exact hA
      · exact hA.modify_eq (by rfl)
    have hk : ∀ eq bond : Option Nat, ({ b1.modify l.owner (fun p => { p with backrow := p.backrow ++
            [{ card := l.card, setTurn := c.turn, faceUp := true, equipTo := eq, bond,
               since := b1.clock + 1, id := b1.clock + 1 }] }) with clock := b1.clock + 1 } : Board).UidOK := by
      intro eq bond
      exact (hA.modify_eq (by rfl)).same rfl rfl rfl
    split
    · exact hk _ _
    · exact hk _ _
    · split
      · split
        · split
          · exact hg
          · exact hk _ _
        · exact hg
      · exact hg
    · exact hg

theorem Board.uidOK_resolveChain (c : Ctx) (ls : List ChainLink) {b : Board} (neg : Bool) (h : b.UidOK) :
    (resolveChain c b neg ls).UidOK := by
  induction ls generalizing b neg with
  | nil => exact h
  | cons l rest ih =>
    simp only [resolveChain]
    apply ih
    split
    · unfold toGrave; split
      · exact h
      · exact h.modify_eq (by rfl)
    · exact Board.uidOK_resolveLink h

theorem Board.UidOK.with_attack {b : Board} (h : b.UidOK) (a : Option AttackDecl) :
    ({ b with attack := a } : Board).UidOK := h.same rfl rfl rfl
theorem Board.UidOK.with_log {b : Board} (h : b.UidOK) (l : List Happened) :
    ({ b with log := l } : Board).UidOK := h.same rfl rfl rfl
theorem Board.UidOK.with_clock {b : Board} (h : b.UidOK) (n : Nat) :
    ({ b with clock := n } : Board).UidOK := h.same rfl rfl rfl
theorem Board.UidOK.with_clock_log {b : Board} (h : b.UidOK) (n : Nat) (l : List Happened) :
    ({ b with clock := n, log := l } : Board).UidOK := h.same rfl rfl rfl
theorem Board.UidOK.with_ns {b : Board} (h : b.UidOK) (x : Bool) :
    ({ b with normalSummoned := x } : Board).UidOK := h.same rfl rfl rfl
theorem Board.UidOK.foldl_toGraveMon {α : Type} {xs : List α} {f : α → Nat} {cause : LeaveCause}
    {b : Board} (h : b.UidOK) : (xs.foldl (fun b x => b.toGraveMon (f x) cause) b).UidOK :=
  h.shrink (Board.shrink_foldl_toGraveMon _ _ _ _)
theorem Board.UidOK.foldl_toGraveMonN {us : List Nat} {cause : LeaveCause}
    {b : Board} (h : b.UidOK) : (us.foldl (fun b u => b.toGraveMon u cause) b).UidOK :=
  h.shrink (Board.shrink_foldl_toGraveMonN _ _ _)

/-- 盤面への操作を外側から1つずつ剥がして、元の盤面の `UidOK` に帰着させる -/
macro "uid_peel" : tactic => `(tactic| repeat' (first
  | with_reducible assumption
  | split
  | with_reducible apply Board.UidOK.toGraveMon
  | with_reducible apply Board.uidOK_place
  | with_reducible apply Board.UidOK.foldl_toGraveMon
  | with_reducible apply Board.UidOK.foldl_toGraveMonN
  | with_reducible refine Board.UidOK.updMon ?_ _ _ _ (fun x => by first | rfl | (split <;> rfl))
  | with_reducible refine Board.UidOK.modify_eq ?_ (by with_unfolding_all rfl)
  | with_reducible refine Board.UidOK.set_eq ?_ (by with_unfolding_all rfl)
  | with_reducible apply Board.UidOK.with_attack
  | with_reducible apply Board.UidOK.with_log
  | with_reducible apply Board.UidOK.with_clock
  | with_reducible apply Board.UidOK.with_ns
  | with_reducible apply Board.UidOK.with_clock_log))

theorem Board.uidOK_performBattle (c : Ctx) {b : Board} (h : b.UidOK) : (performBattle c b).UidOK := by
  unfold performBattle
  dsimp only
  uid_peel
  all_goals exact h.same rfl rfl rfl

theorem Board.shrink_detachAllAux (ms : List FieldMonster) (acc : Board × List FieldMonster) :
    acc.1.Shrink (Board.detachAllAux acc ms).1 := by
  induction ms generalizing acc with
  | nil => exact Board.Shrink.refl _
  | cons m ms ih =>
    simp only [Board.detachAllAux]
    refine Board.Shrink.trans ?_ (ih _)
    split
    · rename_i b x hd; exact Board.shrink_detach hd
    · exact Board.Shrink.refl _

theorem Board.UidOK.detachAll {b : Board} (h : b.UidOK) (ms : List FieldMonster) : (b.detachAll ms).1.UidOK :=
  h.shrink (Board.shrink_detachAllAux ms (b, []))

theorem Board.UidOK.setMonAt {b : Board} {w : PlayerId} {i : Nat} {m m' : FieldMonster} (h : b.UidOK)
    (hm : (b.get w).monsters[i]? = some m) (hu : m'.uid = m.uid) : (b.setMonAt w i m').UidOK :=
  h.shrink (Board.shrink_setMonAt hm hu)

theorem uidOK_pushLink {s s' : ChainState} {b : Board} {l : ChainLink} (hb : b.UidOK)
    (h : pushLink s b l = .ok s') : s'.board.UidOK := by
  rw [(pushLink_ok h).1]; exact hb

theorem uidOK_activateSpellAct {c : Ctx} {s s' : ChainState} {hd : Nat} {args : Args} (hs : s.board.UidOK)
    (h : activateSpellAct c s hd args = .ok s') : s'.board.UidOK := by
  unfold activateSpellAct at h
  simp only [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  repeat' split at h
  all_goals try (cases h; done)
  all_goals exact uidOK_pushLink (hs.set_eq (by rfl)) h

theorem uidOK_activateSetAct {c : Ctx} {s s' : ChainState} {who : PlayerId} {z : Nat} {args : Args}
    (hs : s.board.UidOK) (h : activateSetAct c s who z args = .ok s') : s'.board.UidOK := by
  unfold activateSetAct at h
  simp only [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  repeat' split at h
  all_goals try (cases h; done)
  all_goals exact uidOK_pushLink ((hs.set_eq (by rfl)).modify_eq (by rfl)) h

theorem Board.UidOK.setMonAt_used {b : Board} {w : PlayerId} {i : Nat} {m : FieldMonster} (h : b.UidOK)
    (hm : (b.get w).monsters[i]? = some m) : (b.setMonAt w i { m with effectUsed := true }).UidOK :=
  h.setMonAt hm rfl

theorem uidOK_activateMonsterAct {c : Ctx} {s s' : ChainState} {who : PlayerId} {z i : Nat} {args : Args}
    (hs : s.board.UidOK) (h : activateMonsterAct c s who z i args = .ok s') : s'.board.UidOK := by
  unfold activateMonsterAct at h
  simp only [bind, Except.bind] at h
  repeat' split at h
  all_goals try (simp_all [throw, throwThe, MonadExceptOf.throw]; done)
  all_goals
    apply uidOK_pushLink _ h
    rename_i hv
    simp only [pure, Except.pure, Except.ok.injEq] at hv
    subst hv
  · exact hs.setMonAt_used (by assumption)
  · exact (hs.setMonAt_used (by assumption)).toGraveMon _ _
  · exact (hs.setMonAt_used (by assumption)).modify_eq (by rfl)
  · exact ((hs.setMonAt_used (by assumption)).setMonAt (Board.getElem_setMonAt (by assumption)) (by rfl)).modify_eq
      (by rfl)
  · exact hs.setMonAt_used (by assumption)
  · exact (hs.setMonAt_used (by assumption)).toGraveMon _ _
  · exact (hs.setMonAt_used (by assumption)).modify_eq (by rfl)
  · exact ((hs.setMonAt_used (by assumption)).setMonAt (Board.getElem_setMonAt (by assumption)) (by rfl)).modify_eq
      (by rfl)

theorem uidOK_summonCore {c : Ctx} {b b' : Board} {hd : Nat} {ts : List Nat} {pos : Position}
    (hb : b.UidOK) (h : summonCore c b hd ts pos = .ok b') : b'.UidOK := by
  unfold summonCore at h
  simp only [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  repeat' split at h
  all_goals try (cases h; done)
  all_goals simp only [pure, Except.pure, Except.ok.injEq] at h
  all_goals subst h
  all_goals uid_peel

theorem uidOK_extraSummonAct {c : Ctx} {b b' : Board} {ei : Nat} {ms : List Nat}
    (hb : b.UidOK) (h : extraSummonAct c b ei ms = .ok b') : b'.UidOK := by
  unfold extraSummonAct at h
  simp only [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  repeat' split at h
  all_goals try (cases h; done)
  all_goals simp only [pure, Except.pure, Except.ok.injEq] at h
  all_goals subst h
  · exact Board.uidOK_place (((hb.detachAll _).modify_eq (by rfl)).modify_eq (by rfl)) _ _ _ _ _ _ _
  · exact Board.uidOK_place (hb.foldl_toGraveMon.modify_eq (by rfl)) _ _ _ _ _ _ _
  · exact Board.uidOK_place (((hb.detachAll _).modify_eq (by rfl)).modify_eq (by rfl)) _ _ _ _ _ _ _
  · exact Board.uidOK_place (hb.foldl_toGraveMon.modify_eq (by rfl)) _ _ _ _ _ _ _
  · exact Board.uidOK_place (((hb.detachAll _).modify_eq (by rfl)).modify_eq (by rfl)) _ _ _ _ _ _ _
  · exact Board.uidOK_place (hb.foldl_toGraveMon.modify_eq (by rfl)) _ _ _ _ _ _ _
  · exact Board.uidOK_place (((hb.detachAll _).modify_eq (by rfl)).modify_eq (by rfl)) _ _ _ _ _ _ _
  · exact Board.uidOK_place (hb.foldl_toGraveMon.modify_eq (by rfl)) _ _ _ _ _ _ _

theorem uidOK_boardAct {c : Ctx} {b b' : Board} {a : Action} (hb : b.UidOK) (h : boardAct c b a = .ok b') :
    b'.UidOK := by
  cases a <;> simp only [boardAct] at h
  case normalSummon => exact uidOK_summonCore hb h
  case normalSet => exact uidOK_summonCore hb h
  case extraSummon => exact uidOK_extraSummonAct hb h
  all_goals try (cases h; done)
  all_goals
    simp only [flipSummonAct, changePositionAct, setSpellTrapAct, declareAttack, discardAct, bind, Except.bind,
      throw, throwThe, MonadExceptOf.throw] at h
    repeat' split at h
    all_goals try (cases h; done)
    all_goals simp only [pure, Except.pure, Except.ok.injEq] at h
    all_goals subst h
    all_goals uid_peel

theorem uidOK_passAct (c : Ctx) {s : ChainState} (hs : s.board.UidOK) : (passAct c s).board.UidOK := by
  unfold passAct
  split
  · split
    · exact Board.uidOK_performBattle c hs
    · exact Board.uidOK_resolveChain c _ _ hs
  · exact hs

theorem uidOK_act {c : Ctx} {s s' : ChainState} {a : Action} (hs : s.board.UidOK) (h : act c s a = .ok s') :
    s'.board.UidOK := by
  cases a <;> simp only [act] at h
  case pass => simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; exact uidOK_passAct c hs
  case activateSpell => exact uidOK_activateSpellAct hs h
  case activateSet => exact uidOK_activateSetAct hs h
  case activateMonster => exact uidOK_activateMonsterAct hs h
  all_goals try simp only [throw, throwThe, MonadExceptOf.throw] at h
  all_goals repeat' split at h
  all_goals try (cases h; done)
  all_goals
    obtain ⟨b, hb, rfl⟩ := Except.map_ok h
    exact uidOK_boardAct hs hb

theorem uidOK_processTriggers (c : Ctx) {s : ChainState} (hs : s.board.UidOK) :
    (processTriggers c s).board.UidOK := by
  unfold processTriggers
  split
  · exact hs
  · dsimp only
    split
    · exact hs.with_log _
    · exact hs.with_log _

theorem Player.monsters_resetMonsters_uid (p : Player) :
    p.resetMonsters.monsters.map (·.uid) = p.monsters.map (·.uid) := by
  simp [Player.resetMonsters]

def Game.UidOK (g : Game) : Prop := g.board.UidOK

theorem uidOK_nextPhase {g g' : Game} (hg : g.UidOK) (h : nextPhase g = .ok g') : g'.UidOK := by
  unfold nextPhase at h
  split at h
  all_goals try (simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; exact hg)
  · split at h <;> (simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; exact hg)
  · split at h
    · cases h
    · dsimp only at h
      have h0 : (({ g.board with normalSummoned := false, turnPlayer := g.active.other } : Board).modify g.active Player.resetMonsters).modify
          g.active.other Player.resetMonsters |>.UidOK := by
        refine Board.UidOK.shrink (hg.same rfl rfl rfl) ?_
        refine (Board.shrink_modify ({ g.board with normalSummoned := false, turnPlayer := g.active.other } : Board)
          g.active _ ?_).trans (Board.shrink_modify _ _ _ ?_) <;>
          rw [Player.monsters_resetMonsters_uid] <;> exact List.Sublist.refl _
      split at h
      · simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; exact h0
      · rename_i p hp
        simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
        exact h0.set_eq (Player.monsters_drawOne hp)

theorem Board.UidOK.commitAuras {b : Board} (h : b.UidOK) : b.commitAuras.UidOK := by
  have hu : ∀ (p : Player) w r, (p.commitAuras w r).monsters.map (·.uid) = p.monsters.map (·.uid) := by
    intro p w r; simp [Player.commitAuras, List.map_map, Function.comp_def]
  unfold Board.UidOK Board.uids Board.uidsOf at *
  simpa only [Board.commitAuras, Board.get, hu] using h

theorem Board.UidOK.chooseAura {b b' : Board} {i : Nat} (h : b.UidOK) (hc : b.chooseAura i = .ok b') : b'.UidOK := by
  obtain ⟨r, t, rfl⟩ := Board.chooseAura_ok hc
  have hu : ∀ (p : Player) w r, (p.commitAuras w r).monsters.map (·.uid) = p.monsters.map (·.uid) := by
    intro p w r; simp [Player.commitAuras, List.map_map, Function.comp_def]
  unfold Board.UidOK Board.uids Board.uidsOf at *
  simpa only [Board.get, hu] using h

/-- **1手進めても、フィールドのモンスターの uid は重複しない** -/
theorem step_uidOK {g g' : Game} {a : Action} (hg : g.UidOK) (h : step g a = .ok g') : g'.UidOK := by
  unfold step at h
  split at h
  · cases h
  split at h
  · obtain ⟨i, b, -, hb, rfl⟩ := chooseStep_ok h
    exact (Board.UidOK.chooseAura (show g.board.UidOK from hg) hb).commitAuras
  · split at h
    · split at h
      · exact uidOK_nextPhase hg h
      · cases h
    · cases ha : act g.ctx g.cs a <;> simp only [ha, Except.map] at h
      · cases h
      · rename_i s0
        simp only [Except.ok.injEq] at h; subst h
        exact uidOK_processTriggers g.ctx (uidOK_act (show g.cs.board.UidOK from hg) ha).commitAuras

theorem init_uidOK (d1 d2 e1 e2 : List Card) : (Game.init d1 d2 e1 e2).UidOK := by
  simp [Game.UidOK, Board.UidOK, Board.uids, Board.uidsOf, Board.get, Game.init]

/-- **到達可能な全状態で、フィールドのモンスターの uid は重複しない** -/
theorem reachable_uidOK {g : Game} (hr : Reachable g) : g.UidOK := by
  induction hr with
  | init d1 d2 e1 e2 => exact init_uidOK d1 d2 e1 e2
  | step a _ hs ih => exact step_uidOK ih hs

/-! ## ゾーンの上限 -/

def Player.mainCnt (p : Player) : Nat := (p.monsters.filter (fun m => !m.emz)).length
def Player.emzCnt (p : Player) : Nat := (p.monsters.filter (·.emz)).length

/-- チェーン上の、そのプレイヤーの魔法・罠（魔法・罠ゾーンを使っている） -/
def ownST (ch : List ChainLink) (v : PlayerId) : Nat :=
  (ch.filter (fun l => decide (l.owner = v) && !l.mon)).length

/-- メインモンスターゾーン・エクストラモンスターゾーンの上限と、魔法・罠ゾーンの上限 B -/
def Board.Bounded (b : Board) (B : PlayerId → Nat) : Prop :=
  ∀ v, (b.get v).mainCnt ≤ monsterZones ∧ (b.get v).emzCnt ≤ 1 ∧ (b.get v).backrow.length ≤ B v

/-- ゾーンの上限：チェーン上の魔法・罠も魔法・罠ゾーンを使っている -/
def ZoneOK (b : Board) (ch : List ChainLink) : Prop :=
  ∀ v, (b.get v).mainCnt ≤ monsterZones ∧ (b.get v).emzCnt ≤ 1 ∧
    (b.get v).backrow.length + ownST ch v ≤ spellTrapZones

/-- モンスター・魔法罠が減るか変わらないだけ -/
def Board.Dec (b b' : Board) : Prop :=
  ∀ v, (b'.get v).mainCnt ≤ (b.get v).mainCnt ∧ (b'.get v).emzCnt ≤ (b.get v).emzCnt ∧
    (b'.get v).backrow.length ≤ (b.get v).backrow.length

theorem Board.Dec.refl (b : Board) : b.Dec b := fun _ => ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩

theorem Board.Dec.trans {b b' b'' : Board} (h1 : b.Dec b') (h2 : b'.Dec b'') : b.Dec b'' := fun v =>
  ⟨Nat.le_trans (h2 v).1 (h1 v).1, Nat.le_trans (h2 v).2.1 (h1 v).2.1, Nat.le_trans (h2 v).2.2 (h1 v).2.2⟩

theorem Board.Bounded.dec {b b' : Board} {B : PlayerId → Nat} (h : b.Bounded B) (hd : b.Dec b') :
    b'.Bounded B := fun v =>
  ⟨Nat.le_trans (hd v).1 (h v).1, Nat.le_trans (hd v).2.1 (h v).2.1, Nat.le_trans (hd v).2.2 (h v).2.2⟩

theorem Board.Bounded.mono {b : Board} {B B' : PlayerId → Nat} (h : b.Bounded B) (hB : ∀ v, B v ≤ B' v) :
    b.Bounded B' := fun v => ⟨(h v).1, (h v).2.1, Nat.le_trans (h v).2.2 (hB v)⟩

theorem Player.mainCnt_le_of_sublist {p q : Player} (h : q.monsters.Sublist p.monsters) :
    q.mainCnt ≤ p.mainCnt := (h.filter _).length_le
theorem Player.emzCnt_le_of_sublist {p q : Player} (h : q.monsters.Sublist p.monsters) :
    q.emzCnt ≤ p.emzCnt := (h.filter _).length_le

theorem Board.dec_modify (b : Board) (w : PlayerId) (f : Player → Player)
    (hm : ((f (b.get w)).monsters.filter (fun m => !m.emz)).length ≤ ((b.get w).monsters.filter (fun m => !m.emz)).length)
    (he : ((f (b.get w)).monsters.filter (·.emz)).length ≤ ((b.get w).monsters.filter (·.emz)).length)
    (hb : (f (b.get w)).backrow.length ≤ (b.get w).backrow.length) : b.Dec (b.modify w f) := by
  intro v
  by_cases hv : v = w
  · subst hv; rw [Board.get_modify_same]; exact ⟨hm, he, hb⟩
  · rw [Board.get_modify_other _ _ _ _ hv]; exact ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩

theorem Board.dec_modify_same (b : Board) (w : PlayerId) (f : Player → Player)
    (hm : (f (b.get w)).monsters = (b.get w).monsters)
    (hb : (f (b.get w)).backrow.length ≤ (b.get w).backrow.length) : b.Dec (b.modify w f) :=
  b.dec_modify w f (by rw [hm]; exact Nat.le_refl _) (by rw [hm]; exact Nat.le_refl _) hb

theorem Board.dec_with {b b' : Board} (h1 : b'.p1 = b.p1) (h2 : b'.p2 = b.p2) : b.Dec b' := by
  intro v; cases v <;> simp [Board.get, h1, h2]

theorem length_removeIdxs_fst_le {α : Type} (l : List α) (is : List Nat) : (removeIdxs l is).1.length ≤ l.length := by
  have := removeIdxs_length l is; omega

theorem Board.dec_detach {b b' : Board} {u : Nat} {w : PlayerId} {m : FieldMonster}
    (h : b.detach u = some (b', w, m)) : b.Dec b' := by
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
      obtain ⟨rfl, rfl, rfl⟩ := h
      refine ((b.dec_modify w0 _ ?_ ?_ (Nat.le_refl _)).trans (Board.dec_modify _ _ _ (Nat.le_refl _)
        (Nat.le_refl _) (List.length_filter_le _ _))).trans
        (Board.dec_modify _ _ _ (Nat.le_refl _) (Nat.le_refl _) (List.length_filter_le _ _))
      · exact ((List.eraseIdx_sublist _ _).filter _).length_le
      · exact ((List.eraseIdx_sublist _ _).filter _).length_le

theorem Board.dec_toGraveMon (b : Board) (u : Nat) (cause : LeaveCause) : b.Dec (b.toGraveMon u cause) := by
  unfold Board.toGraveMon
  split
  · exact Board.Dec.refl _
  · rename_i b' w m hd
    refine (Board.dec_detach hd).trans ((b'.dec_modify_same w
      (fun p => { p with grave := p.grave ++ m.overlays ++ [.monster m.card] }) rfl (Nat.le_refl _)).trans ?_)
    by_cases hc : (cause == LeaveCause.sent) = true
    · simp only [hc, ite_true]; exact Board.dec_with rfl rfl
    · simp only [hc, Bool.false_eq_true, ite_false]
      intro v
      cases v <;> cases w <;> simp only [Board.modify, Board.set, Board.get, Player.mainCnt, Player.emzCnt] <;>
        exact ⟨Nat.le_refl _, Nat.le_refl _, length_removeIdxs_fst_le _ _⟩

theorem Board.dec_foldl_toGraveMon {α : Type} (xs : List α) (f : α → Nat) (cause : LeaveCause)
    (b : Board) : b.Dec (xs.foldl (fun b x => b.toGraveMon (f x) cause) b) := by
  induction xs generalizing b with
  | nil => exact Board.Dec.refl _
  | cons x xs ih => exact (Board.dec_toGraveMon _ _ _).trans (ih _)

theorem Board.dec_foldl_toGraveMonN (us : List Nat) (cause : LeaveCause) (b : Board) :
    b.Dec (us.foldl (fun b u => b.toGraveMon u cause) b) := Board.dec_foldl_toGraveMon us id cause b

theorem Board.dec_destroyBackrow (b : Board) (w : PlayerId) (i : Nat) : b.Dec (b.destroyBackrow w i) := by
  unfold Board.destroyBackrow
  split
  · exact Board.Dec.refl _
  · rename_i s _
    have h0 := Board.dec_modify_same b w
      (fun p => { p with backrow := p.backrow.eraseIdx i, grave := p.grave ++ [s.card] }) rfl
      (by simp only [List.length_eraseIdx]; split <;> omega)
    simp only
    split
    · split
      · exact h0
      · exact h0.trans (Board.dec_toGraveMon _ _ _)
    · exact h0

theorem Board.dec_destroyAllBackrow (b : Board) (ws : List PlayerId) : b.Dec (b.destroyAllBackrow ws) := by
  unfold Board.destroyAllBackrow
  simp only
  refine Board.Dec.trans ?_ (Board.dec_foldl_toGraveMonN _ _ _)
  generalize b = b0
  induction ws generalizing b0 with
  | nil => exact Board.Dec.refl _
  | cons w ws ih => exact (Board.dec_modify_same _ _ _ rfl (by simp)).trans (ih _)

theorem Board.dec_detachAllAux (ms : List FieldMonster) (acc : Board × List FieldMonster) :
    acc.1.Dec (Board.detachAllAux acc ms).1 := by
  induction ms generalizing acc with
  | nil => exact Board.Dec.refl _
  | cons m ms ih =>
    simp only [Board.detachAllAux]
    refine Board.Dec.trans ?_ (ih _)
    split
    · rename_i b x hd; exact Board.dec_detach hd
    · exact Board.Dec.refl _

theorem Board.dec_updMon (b : Board) (w : PlayerId) (u : Nat) (f : FieldMonster → FieldMonster)
    (hf : ∀ x, (f x).emz = x.emz) : b.Dec (b.updMon w u f) := by
  unfold Board.updMon
  have key : ∀ (q : FieldMonster → Bool), (∀ x, q (if x.uid = u then f x else x) = q x) →
      (((b.get w).monsters.map fun m => if m.uid = u then f m else m).filter q).length =
        ((b.get w).monsters.filter q).length := by
    intro q hq
    rw [List.filter_map, List.length_map]
    congr 1; apply List.filter_congr; intro x _; simp [Function.comp, hq]
  apply Board.dec_modify
  · rw [key (fun m => !m.emz) (fun x => by split <;> simp [hf])]; exact Nat.le_refl _
  · rw [key (·.emz) (fun x => by split <;> simp [hf])]; exact Nat.le_refl _
  · exact Nat.le_refl _

theorem length_filter_set {α : Type} {l : List α} {i : Nat} {m m' : α} (h : l[i]? = some m)
    (q : α → Bool) (hq : q m' = q m) : ((l.set i m').filter q).length = (l.filter q).length := by
  induction l generalizing i with
  | nil => simp at h
  | cons x xs ih =>
    cases i with
    | zero => simp at h; subst h; simp only [List.set_cons_zero, List.filter_cons, hq]; split <;> simp
    | succ j =>
      simp at h
      simp only [List.set_cons_succ, List.filter_cons]
      split <;> simp [ih h]

theorem Board.dec_setMonAt {b : Board} {w : PlayerId} {i : Nat} {m m' : FieldMonster}
    (h : (b.get w).monsters[i]? = some m) (he : m'.emz = m.emz) : b.Dec (b.setMonAt w i m') := by
  unfold Board.setMonAt
  apply Board.dec_modify
  · rw [length_filter_set h (fun m => !m.emz) (by simp [he])]; exact Nat.le_refl _
  · rw [length_filter_set h (·.emz) (by simp [he])]; exact Nat.le_refl _
  · exact Nat.le_refl _

theorem Player.mainFree_iff (p : Player) : p.mainFree = true ↔ p.mainCnt < monsterZones := by
  simp [Player.mainFree, Player.mainCnt]

theorem Player.slotAfter_nil {p : Player} {isLink e : Bool} (h : p.slotAfter [] isLink = some e) :
    (e = false → p.mainCnt < monsterZones) ∧ (e = true → p.emzCnt = 0) := by
  have hft : ∀ l : List FieldMonster, l.filter (fun _ => true) = l := by
    intro l; induction l <;> simp_all
  unfold Player.slotAfter at h
  simp only [List.contains_nil, Bool.not_false, hft] at h
  split at h
  · rename_i hc; simp at h; subst h
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hc
    exact ⟨fun _ => hc.2, fun h => by simp at h⟩
  · split at h
    · rename_i _ hc; simp at h; subst h
      refine ⟨fun h => by simp at h, fun _ => ?_⟩
      simp only [Bool.not_eq_true', List.any_eq_false] at hc
      simp only [Player.emzCnt, List.length_eq_zero_iff, List.filter_eq_nil_iff]
      intro x hx; simpa using hc x hx
    · simp at h

theorem Board.Bounded.place {b : Board} {B : PlayerId → Nat} (h : b.Bounded B) {w : PlayerId} {c : MonsterCard}
    {pos : Position} {t : Nat} {e : Bool} {ev : Option Event} {ov : List Card}
    (hm : e = false → (b.get w).mainCnt < monsterZones) (he : e = true → (b.get w).emzCnt = 0) :
    (b.place w c pos t e ev ov).Bounded B := by
  intro v
  have hv := h v
  by_cases hvw : v = w
  · subst hvw
    have hg : ((b.place v c pos t e ev ov).get v) = { b.get v with monsters := (b.get v).monsters ++
        [{ uid := b.nextUid, card := c, pos, summonedTurn := t, emz := e, overlays := ov, since := b.clock + 1 }] } := by
      cases v <;> rfl
    rw [hg]
    cases e <;> simp_all [Player.mainCnt, Player.emzCnt, List.filter_append] <;> omega
  · have hg : ((b.place w c pos t e ev ov).get v) = b.get v := by
      cases v <;> cases w <;> first | rfl | exact absurd rfl hvw
    rw [hg]; exact hv

theorem Board.Bounded.place_main {b : Board} {B : PlayerId → Nat} (h : b.Bounded B) {w : PlayerId}
    {c : MonsterCard} {pos : Position} {t : Nat} {ev : Option Event} {ov : List Card}
    (hf : (b.get w).mainFree = true) : (b.place w c pos t false ev ov).Bounded B :=
  h.place (fun _ => (Player.mainFree_iff _).mp hf) (fun h => by simp at h)

theorem Board.Bounded.place_slot {b : Board} {B : PlayerId → Nat} (h : b.Bounded B) {w : PlayerId}
    {c : MonsterCard} {pos : Position} {t : Nat} {e isLink : Bool} {ev : Option Event} {ov : List Card}
    (hs : (b.get w).slotAfter [] isLink = some e) : (b.place w c pos t e ev ov).Bounded B :=
  h.place (Player.slotAfter_nil hs).1 (Player.slotAfter_nil hs).2

theorem Board.Bounded.with_same {b b' : Board} {B : PlayerId → Nat} (h : b.Bounded B)
    (h1 : b'.p1 = b.p1) (h2 : b'.p2 = b.p2) : b'.Bounded B := h.dec (Board.dec_with h1 h2)
theorem Board.Bounded.with_attack {b : Board} {B : PlayerId → Nat} (h : b.Bounded B) (a : Option AttackDecl) :
    ({ b with attack := a } : Board).Bounded B := h.with_same rfl rfl
theorem Board.Bounded.with_log {b : Board} {B : PlayerId → Nat} (h : b.Bounded B) (l : List Happened) :
    ({ b with log := l } : Board).Bounded B := h.with_same rfl rfl
theorem Board.Bounded.with_clock {b : Board} {B : PlayerId → Nat} (h : b.Bounded B) (n : Nat) :
    ({ b with clock := n } : Board).Bounded B := h.with_same rfl rfl
theorem Board.Bounded.with_ns {b : Board} {B : PlayerId → Nat} (h : b.Bounded B) (x : Bool) :
    ({ b with normalSummoned := x } : Board).Bounded B := h.with_same rfl rfl
theorem Board.Bounded.with_clock_log {b : Board} {B : PlayerId → Nat} (h : b.Bounded B) (n : Nat)
    (l : List Happened) : ({ b with clock := n, log := l } : Board).Bounded B := h.with_same rfl rfl
theorem Board.Bounded.toGraveMon {b : Board} {B : PlayerId → Nat} (h : b.Bounded B) (u : Nat) (c : LeaveCause) :
    (b.toGraveMon u c).Bounded B := h.dec (Board.dec_toGraveMon _ _ _)
theorem Board.Bounded.foldl_toGraveMon {α : Type} {xs : List α} {f : α → Nat} {cause : LeaveCause}
    {b : Board} {B : PlayerId → Nat} (h : b.Bounded B) :
    (xs.foldl (fun b x => b.toGraveMon (f x) cause) b).Bounded B := h.dec (Board.dec_foldl_toGraveMon _ _ _ _)
theorem Board.Bounded.foldl_toGraveMonN {us : List Nat} {cause : LeaveCause} {b : Board} {B : PlayerId → Nat}
    (h : b.Bounded B) : (us.foldl (fun b u => b.toGraveMon u cause) b).Bounded B :=
  h.dec (Board.dec_foldl_toGraveMonN _ _ _)
theorem Board.Bounded.modify_same {b : Board} {B : PlayerId → Nat} {w : PlayerId} {f : Player → Player}
    (h : b.Bounded B) (hm : (f (b.get w)).monsters = (b.get w).monsters)
    (hb : (f (b.get w)).backrow.length ≤ (b.get w).backrow.length) : (b.modify w f).Bounded B :=
  h.dec (b.dec_modify_same w f hm hb)
theorem Board.Bounded.set_same {b : Board} {B : PlayerId → Nat} {w : PlayerId} {p : Player}
    (h : b.Bounded B) (hm : p.monsters = (b.get w).monsters) (hb : p.backrow.length ≤ (b.get w).backrow.length) :
    (b.set w p).Bounded B := h.modify_same (f := fun _ => p) hm hb
theorem Board.Bounded.updMon {b : Board} {B : PlayerId → Nat} (h : b.Bounded B) (w : PlayerId) (u : Nat)
    (f : FieldMonster → FieldMonster) (hf : ∀ x, (f x).emz = x.emz) : (b.updMon w u f).Bounded B :=
  h.dec (Board.dec_updMon _ _ _ _ hf)
theorem Board.Bounded.detachAll {b : Board} {B : PlayerId → Nat} (h : b.Bounded B) (ms : List FieldMonster) :
    (b.detachAll ms).1.Bounded B := h.dec (Board.dec_detachAllAux ms (b, []))
theorem Board.Bounded.destroyAllOf {b : Board} {B : PlayerId → Nat} (h : b.Bounded B) (w : PlayerId) :
    (b.destroyAllOf w).Bounded B := h.dec (Board.dec_foldl_toGraveMon _ _ _ _)
theorem Board.Bounded.destroyAllBackrow {b : Board} {B : PlayerId → Nat} (h : b.Bounded B) (ws : List PlayerId) :
    (b.destroyAllBackrow ws).Bounded B := h.dec (Board.dec_destroyAllBackrow _ _)

/-- 盤面への操作を外側から1つずつ剥がして、元の盤面の `Bounded` に帰着させる -/
macro "zone_peel" : tactic => `(tactic| repeat' (first
  | with_reducible assumption
  | split
  | with_reducible apply Board.Bounded.toGraveMon
  | with_reducible apply Board.Bounded.foldl_toGraveMon
  | with_reducible apply Board.Bounded.foldl_toGraveMonN
  | with_reducible apply Board.Bounded.destroyAllOf
  | with_reducible apply Board.Bounded.destroyAllBackrow
  | with_reducible apply Board.Bounded.detachAll
  | (with_reducible refine Board.Bounded.place_main ?_ ?_; with_reducible assumption)
  | (with_reducible refine Board.Bounded.place_slot ?_ ?_; with_reducible assumption)
  | with_reducible refine Board.Bounded.updMon ?_ _ _ _ (fun x => by first | rfl | (split <;> rfl))
  | with_reducible refine Board.Bounded.modify_same ?_ (by with_unfolding_all rfl) (by simp)
  | with_reducible refine Board.Bounded.set_same ?_ (by with_unfolding_all rfl) (by simp)
  | with_reducible apply Board.Bounded.with_attack
  | with_reducible apply Board.Bounded.with_log
  | with_reducible apply Board.Bounded.with_clock
  | with_reducible apply Board.Bounded.with_ns
  | with_reducible apply Board.Bounded.with_clock_log))

theorem Player.slotAfter_monsters {p q : Player} (h : q.monsters = p.monsters) (r : List Nat) (isLink : Bool) :
    q.slotAfter r isLink = p.slotAfter r isLink := by simp [Player.slotAfter, h]

theorem Player.mainFree_monsters {p q : Player} (h : q.monsters = p.monsters) : q.mainFree = p.mainFree := by
  simp [Player.mainFree, h]

theorem Board.get_set_same (b : Board) (w : PlayerId) (p : Player) : (b.set w p).get w = p := by
  cases w <;> rfl

theorem Board.get_set_other (b : Board) (w v : PlayerId) (p : Player) (h : v ≠ w) : (b.set w p).get v = b.get v := by
  cases w <;> cases v <;> simp_all [Board.set, Board.get]

theorem Board.get_modify_monsters (b : Board) (w v : PlayerId) (f : Player → Player)
    (hf : (f (b.get w)).monsters = (b.get w).monsters) : ((b.modify w f).get v).monsters = (b.get v).monsters := by
  by_cases hv : v = w
  · subst hv; rw [Board.get_modify_same, hf]
  · rw [Board.get_modify_other _ _ _ _ hv]

theorem Board.Bounded.place_after_extra {b : Board} {B : PlayerId → Nat} (h : b.Bounded B) {w : PlayerId}
    {i : Nat} {c : MonsterCard} {pos : Position} {t : Nat} {e isLink : Bool} {ev : Option Event}
    {ov : List Card} (hs : (b.get w).slotAfter [] isLink = some e) :
    ((b.modify w fun p => { p with extra := p.extra.eraseIdx i }).place w c pos t e ev ov).Bounded B := by
  apply Board.Bounded.place_slot (isLink := isLink) (h.modify_same rfl (Nat.le_refl _))
  rw [Board.get_modify_same]; exact hs

theorem Player.backrow_drawN {n : Nat} {p p' : Player} (h : p.drawN n = some p') : p'.backrow = p.backrow := by
  induction n generalizing p with
  | zero => simp [Player.drawN] at h; subst h; rfl
  | succ n ih =>
    simp only [Player.drawN, Option.bind_eq_some_iff] at h
    obtain ⟨q, hq, hr⟩ := h
    rw [ih hr]
    unfold Player.drawOne at hq; split at hq <;> simp at hq; subst hq; rfl

theorem Player.backrow_drawOne {p p' : Player} (h : p.drawOne = some p') : p'.backrow = p.backrow := by
  unfold Player.drawOne at h; split at h <;> simp at h; subst h; rfl

theorem reviveOk_mainFree {b : Board} {l : ChainLink} {w : PlayerId} {i : Nat} {m : MonsterCard}
    (h : reviveOk b l = some (w, i, m)) : (b.get l.owner).mainFree = true := by
  unfold reviveOk at h
  split at h
  · split at h
    · rename_i hc; exact hc.2.2
    · simp at h
  · simp at h

/-- **効果を適用してもゾーンの上限を超えない** -/
theorem Board.Bounded.applyEffect {c : Ctx} {l : ChainLink} {b : Board} {B : PlayerId → Nat}
    (h : b.Bounded B) : (applyEffect c l b).Bounded B := by
  unfold YGO.applyEffect
  cases he : l.eff <;> simp only
  case noop => exact h
  case revive own =>
    split
    · exact h
    · rename_i w i m hr
      apply Board.Bounded.place_main (h.modify_same rfl (by simp))
      rw [Player.mainFree_monsters (Board.get_modify_monsters _ _ _ _ rfl)]
      exact reviveOk_mainFree hr
  case fusionSummon =>
    split
    · exact h
    · have h1 : (l.fieldMats.foldl (fun b u => b.toGraveMon u) (b.modify l.owner fun p =>
          let r := removeIdxs p.hand (l.handMats.map (·.1))
          { p with hand := r.1, grave := p.grave ++ r.2 })).Bounded B :=
        (h.modify_same rfl (Nat.le_refl _)).foldl_toGraveMonN
      split
      · exact h1.place_after_extra (by assumption)
      · exact h1
  case recruit =>
    split
    · split
      · split
        · refine Board.Bounded.place_main (h.set_same (by rfl) (by simp)) ?_
          rw [Board.get_set_same]; assumption
        · exact h
      · exact h
    · exact h
  case burn => exact h.modify_same rfl (Nat.le_refl _)
  case heal => exact h.modify_same rfl (Nat.le_refl _)
  case burnPerOppMonster => exact h.modify_same rfl (Nat.le_refl _)
  case millOpp => exact h.modify_same rfl (Nat.le_refl _)
  case draw =>
    split
    · exact h
    · rename_i p hp
      exact h.set_same (Player.monsters_drawN hp) (by rw [Player.backrow_drawN hp]; exact Nat.le_refl _)
  case negate =>
    split
    · exact h
    · rename_i p hp
      exact h.set_same (Player.monsters_drawN hp) (by rw [Player.backrow_drawN hp]; exact Nat.le_refl _)
  case destroyOppMonsters => exact h.destroyAllOf _
  case destroyAllMonsters => exact (h.destroyAllOf _).destroyAllOf _
  case destroyTarget => exact h.foldl_toGraveMonN
  case destroyAttacker =>
    split
    · exact (h.toGraveMon _ _).with_attack _
    · exact h
  case negateAttack => exact h.with_attack _
  case destroyOppSpellTraps => exact h.destroyAllBackrow _
  case destroyAllSpellTraps => exact h.destroyAllBackrow _
  case destroySpellTrap =>
    split
    · split
      · exact h.dec (Board.dec_destroyBackrow _ _ _)
      · exact h
    · exact h
  case searchMaxDef =>
    split
    · split
      · exact h.set_same (by rfl) (by simp)
      · exact h
    · exact h

/-- 魔法・罠ゾーンに戻るカードの分だけ上限を増やす -/
def addST (B : PlayerId → Nat) (l : ChainLink) (v : PlayerId) : Nat :=
  B v + if decide (l.owner = v) && !l.mon then 1 else 0

theorem Board.Bounded.resolveLink {c : Ctx} {b : Board} {l : ChainLink} {B : PlayerId → Nat}
    (h : b.Bounded B) : (resolveLink c b l).Bounded (addST B l) := by
  have hB : ∀ v, B v ≤ addST B l v := fun v => by simp [addST]
  have hA : (if b.effectNegated l then b else YGO.applyEffect c l b).Bounded B := by
    split
    · exact h
    · exact h.applyEffect
  unfold YGO.resolveLink
  simp only
  generalize (if b.effectNegated l then b else YGO.applyEffect c l b) = b1 at hA
  have hg : (toGrave b1 l).Bounded B := by
    unfold toGrave; split
    · exact hA
    · exact hA.modify_same rfl (Nat.le_refl _)
  have hk : ∀ eq bond : Option Nat, l.mon = false →
      ({ b1.modify l.owner (fun p => { p with backrow := p.backrow ++
            [{ card := l.card, setTurn := c.turn, faceUp := true, equipTo := eq, bond,
               since := b1.clock + 1, id := b1.clock + 1 }] }) with clock := b1.clock + 1 } : Board).Bounded (addST B l) := by
    intro eq bond hm
    apply Board.Bounded.with_clock
    intro v
    have hv := hA v
    by_cases hvw : v = l.owner
    · subst hvw
      rw [Board.get_modify_same]
      refine ⟨hv.1, hv.2.1, ?_⟩
      simp [addST, hm]; omega
    · rw [Board.get_modify_other _ _ _ _ hvw]; exact ⟨hv.1, hv.2.1, Nat.le_trans hv.2.2 (hB v)⟩
  split
  · exact hA.mono hB
  · rename_i hm
    simp only [Bool.not_eq_true] at hm
    split
    · exact hk _ _ hm
    · exact hk _ _ hm
    · split
      · split
        · split
          · exact hg.mono hB
          · exact hk _ _ hm
        · exact hg.mono hB
      · exact hg.mono hB
    · exact hg.mono hB

theorem ownST_cons (l : ChainLink) (ls : List ChainLink) (v : PlayerId) :
    ownST (l :: ls) v = (if decide (l.owner = v) && !l.mon then 1 else 0) + ownST ls v := by
  unfold ownST; simp only [List.filter_cons]; split <;> simp_all; omega

theorem Board.Bounded.resolveChain {c : Ctx} (ls : List ChainLink) {b : Board} (neg : Bool) {B : PlayerId → Nat}
    (h : b.Bounded B) : (YGO.resolveChain c b neg ls).Bounded (fun v => B v + ownST ls v) := by
  induction ls generalizing b neg B with
  | nil => simpa [YGO.resolveChain, ownST] using h
  | cons l rest ih =>
    simp only [YGO.resolveChain]
    have h1 : (if neg then toGrave b l else YGO.resolveLink c b l).Bounded (addST B l) := by
      split
      · unfold toGrave; split
        · exact h.mono (fun v => by simp [addST])
        · exact (h.modify_same rfl (Nat.le_refl _)).mono (fun v => by simp [addST])
      · exact h.resolveLink
    refine (ih _ h1).mono (fun v => ?_)
    simp only [addST, ownST_cons]; omega

theorem Board.Bounded.performBattle (c : Ctx) {b : Board} {B : PlayerId → Nat} (h : b.Bounded B) :
    (YGO.performBattle c b).Bounded B := by
  unfold YGO.performBattle
  dsimp only
  repeat' split
  all_goals repeat' (first
    | with_reducible assumption
    | with_reducible apply Board.Bounded.toGraveMon
    | with_reducible refine Board.Bounded.modify_same ?_ (by with_unfolding_all rfl) (Nat.le_refl _)
    | with_reducible refine Board.Bounded.updMon ?_ _ _ _ (fun x => by first | rfl | (split <;> rfl))
    | with_reducible apply Board.Bounded.with_log
    | with_reducible apply Board.Bounded.with_clock
    | with_reducible apply Board.Bounded.with_attack)
  all_goals exact h.with_same rfl rfl

theorem mkLink_owner {b : Board} {who : PlayerId} {card : Card} {eff : Effect} {speed : Nat}
    {args : Args} {shift : Option Nat} {l : ChainLink}
    (h : mkLink b who card eff speed args shift = .ok l) : l.owner = who := by
  unfold mkLink at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals first | (cases h; rfl) | simp_all

theorem ZoneOK.bounded {b : Board} {ch : List ChainLink} (h : ZoneOK b ch) :
    b.Bounded (fun v => spellTrapZones - ownST ch v) := fun v =>
  ⟨(h v).1, (h v).2.1, by show _ ≤ spellTrapZones - ownST ch v; have := (h v).2.2; omega⟩

theorem ZoneOK.of_bounded {b : Board} {ch : List ChainLink} {B : PlayerId → Nat} (h : b.Bounded B)
    (hB : ∀ v, B v + ownST ch v ≤ spellTrapZones) : ZoneOK b ch :=
  fun v => ⟨(h v).1, (h v).2.1, Nat.le_trans (Nat.add_le_add_right (h v).2.2 _) (hB v)⟩

theorem ZoneOK.ownST_le {b : Board} {ch : List ChainLink} (h : ZoneOK b ch) (v : PlayerId) :
    ownST ch v ≤ spellTrapZones := by have := (h v).2.2; omega

theorem Board.dec_setMonAt_used {b : Board} {w : PlayerId} {i : Nat} {m : FieldMonster}
    (h : (b.get w).monsters[i]? = some m) : b.Dec (b.setMonAt w i { m with effectUsed := true }) :=
  Board.dec_setMonAt h rfl

theorem zone_activateMonsterAct {c : Ctx} {s s' : ChainState} {who : PlayerId} {z i : Nat} {args : Args}
    (hs : ZoneOK s.board s.chain) (h : activateMonsterAct c s who z i args = .ok s') :
    ZoneOK s'.board s'.chain := by
  have hb := hs.bounded
  unfold activateMonsterAct at h
  simp only [bind, Except.bind] at h
  repeat' split at h
  all_goals try (simp_all [throw, throwThe, MonadExceptOf.throw]; done)
  all_goals
    obtain ⟨h1, h2⟩ := pushLink_ok h
    rw [h1, h2]
    apply ZoneOK.of_bounded (B := fun v => spellTrapZones - ownST s.chain v)
    rotate_left
    · intro v; rw [ownST_cons]; simp; have := hs.ownST_le v; omega
    rename_i hv
    simp only [pure, Except.pure, Except.ok.injEq] at hv
    subst hv
  all_goals have hu := hb.dec (Board.dec_setMonAt_used (by assumption))
  · exact hu
  · exact hu.toGraveMon _ _
  · exact hu.modify_same rfl (Nat.le_refl _)
  · exact (hu.dec (Board.dec_setMonAt (Board.getElem_setMonAt (by assumption)) (by rfl))).modify_same rfl
      (Nat.le_refl _)
  · exact hu
  · exact hu.toGraveMon _ _
  · exact hu.modify_same rfl (Nat.le_refl _)
  · exact (hu.dec (Board.dec_setMonAt (Board.getElem_setMonAt (by assumption)) (by rfl))).modify_same rfl
      (Nat.le_refl _)

theorem zone_activateSpellAct {c : Ctx} {s s' : ChainState} {hd : Nat} {args : Args}
    (hs : ZoneOK s.board s.chain) (h : activateSpellAct c s hd args = .ok s') : ZoneOK s'.board s'.chain := by
  unfold activateSpellAct at h
  simp only [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  repeat' split at h
  all_goals try (cases h; done)
  have hm := mkLink_mon (by assumption : mkLink _ _ _ _ _ _ _ = .ok _)
  have ho := mkLink_owner (by assumption : mkLink _ _ _ _ _ _ _ = .ok _)
  obtain ⟨h1, h2⟩ := pushLink_ok h
  rw [h1, h2]
  rename_i hfit _ _ _ _ _ _ _
  intro v
  rw [ownST_cons, hm, ho]
  have hv := hs v
  by_cases hvw : v = c.active
  · subst hvw
    rw [Board.get_set_same]
    simp only [decide_true, Bool.not_false, Bool.and_self, ite_true]
    refine ⟨hv.1, hv.2.1, ?_⟩
    simp only [ownST] at hv ⊢; omega
  · have hne : c.active ≠ v := Ne.symm hvw
    rw [Board.get_set_other _ _ _ _ hvw]
    simp only [hne, decide_false, Bool.false_and, Bool.false_eq_true, ite_false, Nat.zero_add]
    exact hv

theorem zone_activateSetAct {c : Ctx} {s s' : ChainState} {who : PlayerId} {z : Nat} {args : Args}
    (hs : ZoneOK s.board s.chain) (h : activateSetAct c s who z args = .ok s') : ZoneOK s'.board s'.chain := by
  unfold activateSetAct at h
  simp only [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  repeat' split at h
  all_goals try (cases h; done)
  all_goals
    have hm := mkLink_mon (by assumption : mkLink _ _ _ _ _ _ _ = .ok _)
    have ho := mkLink_owner (by assumption : mkLink _ _ _ _ _ _ _ = .ok _)
    obtain ⟨_, hz⟩ : ∃ x, (s.board.get who).backrow[z]? = some x := ⟨_, by assumption⟩
    obtain ⟨h1, h2⟩ := pushLink_ok h
    rw [h1, h2]
    intro v
    rw [ownST_cons, hm, ho]
    have hv := hs v
    have hlen := length_eraseIdx_of_getElem? hz
    by_cases hvw : v = who
    · subst hvw
      rw [Board.get_modify_same, Board.get_set_same]
      simp only [decide_true, Bool.not_false, Bool.and_self, ite_true]
      refine ⟨hv.1, hv.2.1, ?_⟩
      simp only [Player.damage] at hlen ⊢; omega
    · have hne : who ≠ v := Ne.symm hvw
      rw [Board.get_modify_other _ _ _ _ hvw]
      rw [Board.get_set_other _ _ _ _ hvw]
      simp only [hne, decide_false, Bool.false_and, Bool.false_eq_true, ite_false, Nat.zero_add]
      exact hv

abbrev full : PlayerId → Nat := fun _ => spellTrapZones

theorem zone_summonCore {c : Ctx} {b b' : Board} {hd : Nat} {ts : List Nat} {pos : Position}
    (hb : b.Bounded full) (h : summonCore c b hd ts pos = .ok b') : b'.Bounded full := by
  unfold summonCore at h
  simp only [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  repeat' split at h
  all_goals try (cases h; done)
  all_goals simp only [pure, Except.pure, Except.ok.injEq] at h
  all_goals subst h
  all_goals
    apply Board.Bounded.with_ns
    exact Board.Bounded.place_main (hb.foldl_toGraveMon.modify_same rfl (Nat.le_refl _)) (by assumption)

theorem zone_extraSummonAct {c : Ctx} {b b' : Board} {ei : Nat} {ms : List Nat}
    (hb : b.Bounded full) (h : extraSummonAct c b ei ms = .ok b') : b'.Bounded full := by
  unfold extraSummonAct at h
  simp only [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  repeat' split at h
  all_goals try (cases h; done)
  all_goals simp only [pure, Except.pure, Except.ok.injEq] at h
  all_goals subst h
  · exact ((hb.detachAll _).modify_same rfl (Nat.le_refl _)).place_after_extra (by assumption)
  · exact hb.foldl_toGraveMon.place_after_extra (by assumption)
  · exact ((hb.detachAll _).modify_same rfl (Nat.le_refl _)).place_after_extra (by assumption)
  · exact hb.foldl_toGraveMon.place_after_extra (by assumption)
  · exact ((hb.detachAll _).modify_same rfl (Nat.le_refl _)).place_after_extra (by assumption)
  · exact hb.foldl_toGraveMon.place_after_extra (by assumption)
  · exact ((hb.detachAll _).modify_same rfl (Nat.le_refl _)).place_after_extra (by assumption)
  · exact hb.foldl_toGraveMon.place_after_extra (by assumption)

theorem zone_boardAct {c : Ctx} {b b' : Board} {a : Action} (hb : b.Bounded full) (h : boardAct c b a = .ok b') :
    b'.Bounded full := by
  cases a <;> simp only [boardAct] at h
  case normalSummon => exact zone_summonCore hb h
  case normalSet => exact zone_summonCore hb h
  case extraSummon => exact zone_extraSummonAct hb h
  case setSpellTrap =>
    simp only [setSpellTrapAct, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
    repeat' split at h
    all_goals try (cases h; done)
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    rename_i hlt
    apply Board.Bounded.with_clock
    intro v
    have hv := hb v
    by_cases hvw : v = c.active
    · subst hvw
      rw [Board.get_set_same]
      refine ⟨hv.1, hv.2.1, ?_⟩
      simp only [List.length_append, List.length_cons, List.length_nil]; exact hlt
    · rw [Board.get_set_other _ _ _ _ hvw]; exact hv
  case discard =>
    simp only [discardAct, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
    repeat' split at h
    all_goals try (cases h; done)
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact hb.set_same rfl (Nat.le_refl _)
  all_goals try (cases h; done)
  all_goals
    simp only [flipSummonAct, changePositionAct, declareAttack, bind, Except.bind,
      throw, throwThe, MonadExceptOf.throw] at h
    repeat' split at h
    all_goals try (cases h; done)
    all_goals simp only [pure, Except.pure, Except.ok.injEq] at h
    all_goals subst h
  all_goals first
    | exact (hb.updMon _ _ _ (fun _ => by rfl)).with_clock_log _ _
    | exact hb.updMon _ _ _ (fun _ => by rfl)
    | exact (hb.updMon _ _ _ (fun _ => by rfl)).with_attack _

theorem ownST_nil (v : PlayerId) : ownST [] v = 0 := rfl

theorem zone_passAct (c : Ctx) {s : ChainState} (hs : ZoneOK s.board s.chain) :
    ZoneOK (passAct c s).board (passAct c s).chain := by
  unfold passAct
  split
  · split
    · rename_i he
      simp only [List.isEmpty_iff] at he
      rw [he] at hs
      refine ZoneOK.of_bounded (B := full) ((hs.bounded.mono (fun v => by simp [ownST_nil])).performBattle c)
        (fun v => by simp [ownST_nil])
    · refine ZoneOK.of_bounded (hs.bounded.resolveChain s.chain false) (fun v => ?_)
      simp only [ownST_nil]; have := hs.ownST_le v; omega
  · exact hs

theorem zone_act {c : Ctx} {s s' : ChainState} {a : Action} (hs : ZoneOK s.board s.chain)
    (h : act c s a = .ok s') : ZoneOK s'.board s'.chain := by
  cases a <;> simp only [act] at h
  case pass => simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; exact zone_passAct c hs
  case activateSpell => exact zone_activateSpellAct hs h
  case activateSet => exact zone_activateSetAct hs h
  case activateMonster => exact zone_activateMonsterAct hs h
  all_goals try simp only [throw, throwThe, MonadExceptOf.throw] at h
  all_goals repeat' split at h
  all_goals try (cases h; done)
  all_goals
    rename_i hc _ _
    simp only [Bool.not_eq_true', List.isEmpty_eq_false_iff, ne_eq, Decidable.not_not] at hc
    obtain ⟨b, hb, rfl⟩ := Except.map_ok h
    rw [hc] at hs ⊢
    exact ZoneOK.of_bounded (zone_boardAct ((hs.bounded).mono (fun v => by simp [ownST_nil])) hb)
      (fun v => by simp [ownST_nil])

theorem ownST_all_mon {ls : List ChainLink} {v : PlayerId} (h : ∀ l ∈ ls, l.mon = true) : ownST ls v = 0 := by
  unfold ownST
  simp only [List.length_eq_zero_iff, List.filter_eq_nil_iff, Bool.and_eq_true, Bool.not_eq_true', not_and,
    Bool.not_eq_false]
  intro l hl _; exact h l hl

theorem zone_processTriggers (c : Ctx) {s : ChainState} (hs : ZoneOK s.board s.chain) :
    ZoneOK (processTriggers c s).board (processTriggers c s).chain := by
  unfold processTriggers
  split
  · exact hs
  · rename_i hc
    simp only [Bool.not_eq_true', List.isEmpty_eq_false_iff, ne_eq, Decidable.not_not] at hc
    dsimp only
    rw [hc] at hs
    have hb : ({ s.board with log := [] } : Board).Bounded full :=
      (hs.bounded.mono (fun v => by simp [ownST_nil])).with_log _
    split
    · rw [hc]; exact ZoneOK.of_bounded hb (fun v => by simp [ownST_nil])
    · refine ZoneOK.of_bounded hb (fun v => ?_)
      rw [ownST_all_mon]
      · simp
      · intro l hl
        simp only [List.mem_reverse, List.mem_append, List.mem_filter, List.mem_flatMap] at hl
        rcases hl with ⟨⟨h, _, hl⟩, _⟩ | ⟨⟨h, _, hl⟩, _⟩ <;> exact triggeredLinks_mon hl

def Game.ZoneOK (g : Game) : Prop := YGO.ZoneOK g.board g.chain

theorem Player.resetMonsters_emz (p : Player) :
    p.resetMonsters.mainCnt = p.mainCnt ∧ p.resetMonsters.emzCnt = p.emzCnt := by
  simp only [Player.resetMonsters, Player.mainCnt, Player.emzCnt, List.filter_map, List.length_map]
  exact ⟨rfl, rfl⟩

theorem zone_nextPhase {g g' : Game} (hg : g.ZoneOK) (h : nextPhase g = .ok g') : g'.ZoneOK := by
  unfold nextPhase at h
  split at h
  all_goals try (simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; exact hg)
  · split at h <;> (simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; exact hg)
  · split at h
    · cases h
    · dsimp only at h
      have hb := hg
      unfold Game.ZoneOK at hb
      have h0 : ((({ g.board with normalSummoned := false, turnPlayer := g.active.other } : Board).modify g.active Player.resetMonsters).modify
          g.active.other Player.resetMonsters).Bounded (fun v => spellTrapZones - ownST g.chain v) := by
        have hr : ∀ (b : Board) (w : PlayerId), b.Dec (b.modify w Player.resetMonsters) := fun b w =>
          b.dec_modify w _ (Nat.le_of_eq (Player.resetMonsters_emz _).1)
            (Nat.le_of_eq (Player.resetMonsters_emz _).2) (Nat.le_refl _)
        exact (((hb.bounded).with_same (b' := ({ g.board with normalSummoned := false, turnPlayer := g.active.other } : Board)) rfl rfl).dec
          (hr _ g.active)).dec (hr _ _)
      split at h
      · simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
        exact ZoneOK.of_bounded (ch := g.chain) h0 (fun v => by have := hb.ownST_le v; omega)
      · rename_i p hp
        simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
        refine ZoneOK.of_bounded (ch := g.chain) (h0.set_same (Player.monsters_drawOne hp) ?_)
          (fun v => by have := hb.ownST_le v; omega)
        rw [Player.backrow_drawOne hp]; exact Nat.le_refl _

theorem ZoneOK.commitAuras {b : Board} {ch : List ChainLink} (h : ZoneOK b ch) : ZoneOK b.commitAuras ch := by
  have he : ∀ (p : Player) w r, (p.commitAuras w r).mainCnt = p.mainCnt ∧
      (p.commitAuras w r).emzCnt = p.emzCnt ∧ (p.commitAuras w r).backrow.length = p.backrow.length := by
    intro p w r
    simp [Player.commitAuras, Player.mainCnt, Player.emzCnt, List.filter_map, Function.comp_def]
  intro v
  obtain ⟨h1, h2, h3⟩ := h v
  cases v
  · obtain ⟨e1, e2, e3⟩ := he b.p1 .one (settle b.sources b.clock b.turnPlayer).1
    exact ⟨by simpa [Board.commitAuras, Board.get, e1] using h1, by simpa [Board.commitAuras, Board.get, e2] using h2,
      by simpa [Board.commitAuras, Board.get, e3] using h3⟩
  · obtain ⟨e1, e2, e3⟩ := he b.p2 .two (settle b.sources b.clock b.turnPlayer).1
    exact ⟨by simpa [Board.commitAuras, Board.get, e1] using h1, by simpa [Board.commitAuras, Board.get, e2] using h2,
      by simpa [Board.commitAuras, Board.get, e3] using h3⟩

theorem ZoneOK.chooseAura {b b' : Board} {ch : List ChainLink} {i : Nat} (h : ZoneOK b ch)
    (hc : b.chooseAura i = .ok b') : ZoneOK b' ch := by
  obtain ⟨r, t, rfl⟩ := Board.chooseAura_ok hc
  have he : ∀ (p : Player) w r, (p.commitAuras w r).mainCnt = p.mainCnt ∧
      (p.commitAuras w r).emzCnt = p.emzCnt ∧ (p.commitAuras w r).backrow.length = p.backrow.length := by
    intro p w r
    simp [Player.commitAuras, Player.mainCnt, Player.emzCnt, List.filter_map, Function.comp_def]
  intro v
  obtain ⟨h1, h2, h3⟩ := h v
  cases v
  · obtain ⟨e1, e2, e3⟩ := he b.p1 .one r
    exact ⟨by simpa [Board.get, e1] using h1, by simpa [Board.get, e2] using h2, by simpa [Board.get, e3] using h3⟩
  · obtain ⟨e1, e2, e3⟩ := he b.p2 .two r
    exact ⟨by simpa [Board.get, e1] using h1, by simpa [Board.get, e2] using h2, by simpa [Board.get, e3] using h3⟩

/-- **1手進めても、ゾーンの上限を超えない** -/
theorem step_zoneOK {g g' : Game} {a : Action} (hg : g.ZoneOK) (h : step g a = .ok g') : g'.ZoneOK := by
  unfold step at h
  split at h
  · cases h
  split at h
  · obtain ⟨i, b, -, hb, rfl⟩ := chooseStep_ok h
    exact (ZoneOK.chooseAura (ch := g.chain) hg hb).commitAuras
  · split at h
    · split at h
      · exact zone_nextPhase hg h
      · cases h
    · cases ha : act g.ctx g.cs a <;> simp only [ha, Except.map] at h
      · cases h
      · rename_i s0
        simp only [Except.ok.injEq] at h; subst h
        exact zone_processTriggers g.ctx (zone_act (s := g.cs) hg ha).commitAuras

/-- **到達可能な全状態で、ゾーンの上限を超えない**（初期状態でフィールドが空であることから） -/
theorem reachable_zoneOK {g : Game} (hr : Reachable g) : g.ZoneOK := by
  induction hr with
  | init d1 d2 e1 e2 =>
    intro v; cases v <;> simp [Game.init, Board.get, Player.mainCnt, Player.emzCnt, ownST, monsterZones,
      spellTrapZones]
  | step a _ hs ih => exact step_zoneOK ih hs

/-! ## LP と勝敗 -/

/-- 決着がついていなければ、両者の LP は 1 以上 -/
def Game.LPOK (g : Game) : Prop := g.result = none → 0 < g.board.p1.lp ∧ 0 < g.board.p2.lp

theorem checkResult_none {g : Game} (h : (checkResult g).result = none) :
    0 < g.board.p1.lp ∧ 0 < g.board.p2.lp := by
  unfold checkResult at h
  simp only at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · split at h
      · simp at h
      · split at h
        · simp at h
        · rename_i h1 h2 h3; omega

theorem Board.lp_modify_reset (b : Board) (w v : PlayerId) :
    ((b.modify w Player.resetMonsters).get v).lp = (b.get v).lp := by
  by_cases hv : v = w
  · subst hv; rw [Board.get_modify_same]; rfl
  · rw [Board.get_modify_other _ _ _ _ hv]

theorem Player.lp_drawOne {p p' : Player} (h : p.drawOne = some p') : p'.lp = p.lp := by
  unfold Player.drawOne at h; split at h <;> simp at h; subst h; rfl

theorem Board.lp_p (b : Board) : b.p1 = b.get .one ∧ b.p2 = b.get .two := ⟨rfl, rfl⟩

/-- フェイズの移行では LP は変わらない -/
theorem nextPhase_lp {g g' : Game} (h : nextPhase g = .ok g') :
    ∀ v, (g'.board.get v).lp = (g.board.get v).lp := by
  intro v
  unfold nextPhase at h
  split at h
  all_goals try (simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; rfl)
  · split at h <;> (simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; rfl)
  · split at h
    · cases h
    · dsimp only at h
      split at h
      · simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
        simp only [Board.lp_modify_reset]; cases v <;> rfl
      · rename_i p hp
        simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
        by_cases hv : v = g.active.other
        · subst hv; rw [Board.get_set_same, Player.lp_drawOne hp]; simp only [Board.lp_modify_reset]
          cases g.active <;> rfl
        · rw [Board.get_set_other _ _ _ _ hv]; simp only [Board.lp_modify_reset]; cases v <;> rfl

/-- **1手進めても、決着がついていないなら両者の LP は 1 以上** -/
theorem step_LPOK {g g' : Game} {a : Action} (hg : g.LPOK) (h : step g a = .ok g') : g'.LPOK := by
  intro hr
  unfold step at h
  split at h
  · cases h
  rename_i hn
  split at h
  · obtain ⟨i, b, -, -, rfl⟩ := chooseStep_ok h
    exact checkResult_none (g := { g with board := b.commitAuras }) hr
  · split at h
    · split at h
      · have hl := nextPhase_lp h
        have hgn : g.result = none := by simpa using hn
        obtain ⟨h1, h2⟩ := hg hgn
        rw [(Board.lp_p _).1, (Board.lp_p _).2, hl .one, hl .two]; exact ⟨h1, h2⟩
      · cases h
    · cases ha : act g.ctx g.cs a <;> simp only [ha, Except.map] at h
      · cases h
      · rename_i s0
        simp only [Except.ok.injEq] at h; subst h
        exact checkResult_none (g := g.setCs (processTriggers g.ctx { s0 with board := s0.board.commitAuras })) hr

theorem reachable_LPOK {g : Game} (hr : Reachable g) : g.LPOK := by
  induction hr with
  | init d1 d2 e1 e2 => intro _; simp [Game.init, initialLP]
  | step a _ hs ih => exact step_LPOK ih hs

/-- **到達可能な全状態で、どちらかの LP が 0 なら決着がついている** -/
theorem reachable_lp_zero_decided {g : Game} (hr : Reachable g)
    (h0 : g.board.p1.lp = 0 ∨ g.board.p2.lp = 0) : g.result.isSome := by
  have := reachable_LPOK hr
  cases hres : g.result with
  | some _ => rfl
  | none => obtain ⟨h1, h2⟩ := this hres; omega

/-! ## 永続効果の有効・無効の判定（settle）の正しさ
`settleOnce` がこれ以上状態を変えない（判定が決まったか、プレイヤーの選択待ちの）とき、次が成り立つ。 -/

theorem filter_range_mem {n : Nat} {l : List AuraSrc} {P : AuraSrc → Bool} {j : Nat}
    (h : j ∈ (List.range n).filter fun j => l[j]?.any P) : ∃ hj : j < l.length, P l[j] = true := by
  simp only [List.mem_filter, List.mem_range] at h
  obtain ⟨-, ha⟩ := h
  cases hj : l[j]? with
  | none => rw [hj] at ha; cases ha
  | some s =>
    obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.mp hj
    rw [hj] at ha; exact ⟨hlt, by simpa using ha⟩

/-- 有効に戻せるカードは、無効で、どの適用中のカードにも無効にされない -/
theorem returnCands_mem {srcs : List AuraSrc} {tp : PlayerId} {j : Nat} (h : j ∈ returnCands srcs tp) :
    ∃ hj : j < srcs.length, srcs[j].on = false ∧ beatenIn srcs srcs[j] = false := by
  unfold returnCands at h
  simp only at h
  split at h
  · obtain ⟨hj, ha⟩ := filter_range_mem h
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at ha
    exact ⟨hj, ha⟩
  · obtain ⟨hj, ha⟩ := filter_range_mem h
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at ha
    exact ⟨hj, ha.2⟩

/-- 有効に戻せるカードがなければ、無効なカードはどれも適用中のカードに無効にされている -/
theorem returnCands_nil {srcs : List AuraSrc} {tp : PlayerId} (h : returnCands srcs tp = []) :
    ∀ s ∈ srcs, (!s.on && !beatenIn srcs s) = false := by
  unfold returnCands at h
  simp only at h
  split at h
  · intro s hs
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hs
    have := List.filter_eq_nil_iff.mp h j (List.mem_range.mpr hj)
    simpa [List.getElem?_eq_getElem hj] using this
  · rename_i hm; rw [h] at hm; simp at hm

theorem settleOnce_none {srcs : List AuraSrc} {c : Nat} {tp : PlayerId} (h : settleOnce srcs c tp = none) :
    (∀ s ∈ srcs, s.on = true → beatenIn srcs s = false) ∧
    (awaitingChoice srcs tp = none → ∀ s ∈ srcs, s.on = false → beatenIn srcs s = true) := by
  unfold settleOnce at h
  split at h
  · cases h
  rename_i h1
  rw [List.findIdx?_eq_none_iff] at h1
  refine ⟨fun s hs ho => by simpa [ho] using h1 s hs, fun hw s hs ho => ?_⟩
  have hk : srcs.any (fun s => s.on && beatenIn srcs s) = false := by
    simpa using h1
  unfold awaitingChoice at hw
  rw [hk] at hw
  simp only [Bool.false_eq_true, ite_false] at hw
  split at h
  · cases h
  rename_i h2
  cases hc : returnCands srcs tp with
  | nil => simpa [ho] using returnCands_nil hc s hs
  | cons i rest =>
    cases rest with
    | nil => exact absurd hc (h2 i)
    | cons j rest =>
      rw [hc] at hw
      obtain ⟨hi, -⟩ := returnCands_mem (hc ▸ List.mem_cons_self : i ∈ returnCands srcs tp)
      simp [List.getElem?_eq_getElem hi] at hw

/-- **有効なカード同士は、互いに無効にしない** -/
theorem settled_consistent {srcs : List AuraSrc} {c : Nat} {tp : PlayerId} (h : settleOnce srcs c tp = none)
    {s t : AuraSrc} (hs : s ∈ srcs) (ht : t ∈ srcs) (hso : s.on = true) (hto : t.on = true) :
    t.beats s = false := by
  have := (settleOnce_none h).1 s hs hso
  simp only [beatenIn, List.any_eq_false, Bool.and_eq_true, not_and] at this
  cases hb : t.beats s
  · rfl
  · exact absurd hb (this t ht hto)

/-- **無効なカードには、それを無効にする有効なカードがある** -/
theorem negated_has_reason {srcs : List AuraSrc} {c : Nat} {tp : PlayerId} (h : settleOnce srcs c tp = none)
    (hw : awaitingChoice srcs tp = none) {s : AuraSrc} (hs : s ∈ srcs) (hso : s.on = false) :
    ∃ t ∈ srcs, t.on = true ∧ t.beats s = true := by
  have := (settleOnce_none h).2 hw s hs hso
  simpa [beatenIn] using this

/-- **どのカードにも無効にされないカードは有効** -/
theorem unbeaten_effective {srcs : List AuraSrc} {c : Nat} {tp : PlayerId} (h : settleOnce srcs c tp = none)
    (hw : awaitingChoice srcs tp = none) {s : AuraSrc} (hs : s ∈ srcs) (hn : ∀ t ∈ srcs, t.beats s = false) :
    s.on = true := by
  cases hso : s.on
  · obtain ⟨t, ht, _, hb⟩ := negated_has_reason h hw hs hso
    rw [hn t ht] at hb; cases hb
  · rfl

theorem map_modify_eq {α β : Type} (l : List α) (f : α → α) (g : α → β) (hf : ∀ x, g (f x) = g x) (i : Nat) :
    (l.modify i f).map g = l.map g := by
  induction l generalizing i with
  | nil => simp
  | cons x xs ih => cases i <;> simp [hf, ih]

/-- `settleOnce` は有効・無効と適用の時刻だけを変える -/
theorem settleOnce_keys {srcs srcs' : List AuraSrc} {c c' : Nat} {tp : PlayerId} (h : settleOnce srcs c tp = some (srcs', c')) :
    srcs'.map (fun s => (s.who, s.kind, s.key, s.auras)) = srcs.map (fun s => (s.who, s.kind, s.key, s.auras)) := by
  unfold settleOnce at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
    apply map_modify_eq; intro; rfl
  · split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
      apply map_modify_eq; intro; rfl
    · cases h

/-- **判定で変わるのは有効・無効と適用の時刻だけで、カードの集まりは変わらない** -/
theorem settle_keys (srcs : List AuraSrc) (c : Nat) (tp : PlayerId) :
    (settle srcs c tp).1.map (fun s => (s.who, s.kind, s.key, s.auras)) =
      srcs.map (fun s => (s.who, s.kind, s.key, s.auras)) := by
  unfold settle
  generalize 4 * (3 * srcs.length + 1) ^ 4 = n
  induction n generalizing srcs c with
  | zero => rfl
  | succ n ih =>
    simp only [settleAux]
    split
    · rename_i srcs' c' h; rw [ih, settleOnce_keys h]
    · rfl

end YGO

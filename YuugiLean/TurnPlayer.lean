import YuugiLean.Invariants

/-!
# 盤面のターンプレイヤー

盤面は、同時に有効に戻る永続効果の適用順（②）のためにターンプレイヤー（`Board.turnPlayer`）を持つ。
これを変えるのはフェイズの移行（ターンの交代）だけで、到達可能などの状態でも対戦のターンプレイヤー
（`Game.active`）と一致する（`reachable_turnPlayer`）。
-/

namespace YGO

@[simp] theorem Board.tp_set (b : Board) (w : PlayerId) (p : Player) : (b.set w p).turnPlayer = b.turnPlayer := by
  cases w <;> rfl

@[simp] theorem Board.tp_modify (b : Board) (w : PlayerId) (f : Player → Player) :
    (b.modify w f).turnPlayer = b.turnPlayer := by
  cases w <;> rfl

@[simp] theorem Board.tp_updMon (b : Board) (w : PlayerId) (u : Nat) (f : FieldMonster → FieldMonster) :
    (b.updMon w u f).turnPlayer = b.turnPlayer := by
  simp [Board.updMon]

@[simp] theorem Board.tp_setMonAt (b : Board) (w : PlayerId) (i : Nat) (m : FieldMonster) :
    (b.setMonAt w i m).turnPlayer = b.turnPlayer := by
  simp [Board.setMonAt]

@[simp] theorem Board.tp_place (b : Board) (w : PlayerId) (c : MonsterCard) (pos : Position) (t : Nat)
    (emz : Bool) (ev : Option Event) (ov : List Card) :
    (b.place w c pos t emz ev ov).turnPlayer = b.turnPlayer := by
  simp [Board.place]

theorem Board.tp_detach {b b' : Board} {u : Nat} {w : PlayerId} {m : FieldMonster}
    (h : b.detach u = some (b', w, m)) : b'.turnPlayer = b.turnPlayer := by
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
      simp

@[simp] theorem Board.tp_toGraveMon (b : Board) (u : Nat) (cause : LeaveCause) :
    (b.toGraveMon u cause).turnPlayer = b.turnPlayer := by
  unfold Board.toGraveMon
  split
  · rfl
  · rename_i b' w m h
    have := Board.tp_detach h
    dsimp only
    split <;> simp [this]

theorem foldl_tp {α : Type} (xs : List α) (f : Board → α → Board)
    (hf : ∀ b x, (f b x).turnPlayer = b.turnPlayer) (b : Board) : (xs.foldl f b).turnPlayer = b.turnPlayer := by
  induction xs generalizing b with
  | nil => rfl
  | cons x xs ih => simp only [List.foldl_cons]; rw [ih, hf]

theorem Board.tp_detachAllAux (ms : List FieldMonster) (acc : Board × List FieldMonster) :
    (Board.detachAllAux acc ms).1.turnPlayer = acc.1.turnPlayer := by
  induction ms generalizing acc with
  | nil => rfl
  | cons m ms ih =>
    simp only [Board.detachAllAux]
    rw [ih]
    split
    · rename_i b _ x h; exact Board.tp_detach h
    · rfl

@[simp] theorem Board.tp_detachAll (b : Board) (ms : List FieldMonster) :
    (b.detachAll ms).1.turnPlayer = b.turnPlayer :=
  Board.tp_detachAllAux ms (b, [])

@[simp] theorem Board.tp_destroyAllOf (b : Board) (w : PlayerId) : (b.destroyAllOf w).turnPlayer = b.turnPlayer :=
  foldl_tp _ _ (fun _ _ => Board.tp_toGraveMon _ _ _) _

@[simp] theorem Board.tp_destroyBackrow (b : Board) (w : PlayerId) (i : Nat) :
    (b.destroyBackrow w i).turnPlayer = b.turnPlayer := by
  unfold Board.destroyBackrow
  split
  · rfl
  · dsimp only; split
    · split <;> simp
    · simp

@[simp] theorem Board.tp_destroyAllBackrow (b : Board) (ws : List PlayerId) :
    (b.destroyAllBackrow ws).turnPlayer = b.turnPlayer := by
  unfold Board.destroyAllBackrow
  dsimp only
  rw [foldl_tp _ _ (fun _ _ => Board.tp_toGraveMon _ _ _), foldl_tp _ _ (fun _ _ => Board.tp_modify _ _ _)]

@[simp] theorem Board.tp_equipMon (b : Board) (v : PlayerId) (s u t : Nat) :
    (b.equipMon v s u t).turnPlayer = b.turnPlayer := by
  unfold Board.equipMon
  split
  · rename_i b' w m h
    have := Board.tp_detach h
    simp [this]
  · rfl

@[simp] theorem Board.tp_applyEffect (c : Ctx) (l : ChainLink) (b : Board) :
    (applyEffect c l b).turnPlayer = b.turnPlayer := by
  unfold applyEffect
  split <;> (try dsimp only) <;> (repeat' split) <;>
    simp [foldl_tp _ _ (fun _ _ => Board.tp_toGraveMon _ _ _)]

@[simp] theorem Board.tp_toGrave (b : Board) (l : ChainLink) : (toGrave b l).turnPlayer = b.turnPlayer := by
  unfold toGrave; split <;> simp

@[simp] theorem Board.tp_resolveLink (c : Ctx) (b : Board) (l : ChainLink) :
    (resolveLink c b l).turnPlayer = b.turnPlayer := by
  unfold resolveLink
  dsimp only
  repeat' split
  all_goals simp

@[simp] theorem Board.tp_resolveChain (c : Ctx) (ls : List ChainLink) (b : Board) (neg : Bool) :
    (resolveChain c b neg ls).turnPlayer = b.turnPlayer := by
  induction ls generalizing b neg with
  | nil => rfl
  | cons l ls ih => simp only [resolveChain]; rw [ih]; split <;> simp

theorem tp_pushLink {s s' : ChainState} {b : Board} {l : ChainLink} (h : pushLink s b l = .ok s') :
    s'.board.turnPlayer = b.turnPlayer := by
  rw [(pushLink_ok h).1]

theorem tp_activateSpellAct {c : Ctx} {s s' : ChainState} {hd : Nat} {args : Args}
    (h : activateSpellAct c s hd args = .ok s') : s'.board.turnPlayer = s.board.turnPlayer := by
  unfold activateSpellAct at h
  simp only [bind, Except.bind] at h
  repeat' split at h
  all_goals try (simp_all [throw, throwThe, MonadExceptOf.throw]; done)
  rw [tp_pushLink h]; simp

theorem tp_activateSetAct {c : Ctx} {s s' : ChainState} {who : PlayerId} {z : Nat} {args : Args}
    (h : activateSetAct c s who z args = .ok s') : s'.board.turnPlayer = s.board.turnPlayer := by
  unfold activateSetAct at h
  simp only [bind, Except.bind] at h
  repeat' split at h
  all_goals try (simp_all [throw, throwThe, MonadExceptOf.throw]; done)
  all_goals (rw [tp_pushLink h]; simp)

theorem tp_activateMonsterAct {c : Ctx} {s s' : ChainState} {who : PlayerId} {z i : Nat} {args : Args}
    (h : activateMonsterAct c s who z i args = .ok s') : s'.board.turnPlayer = s.board.turnPlayer := by
  unfold activateMonsterAct at h
  simp only [bind, Except.bind] at h
  repeat' split at h
  all_goals try (simp_all [throw, throwThe, MonadExceptOf.throw]; done)
  all_goals
    rw [tp_pushLink h]
    rename_i hv
    simp only [pure, Except.pure, Except.ok.injEq] at hv
    subst hv
    simp

theorem tp_summonCore {c : Ctx} {b b' : Board} {hd : Nat} {ts : List Nat} {pos : Position} {sp : Bool}
    (h : summonCore c b hd ts pos sp = .ok b') : b'.turnPlayer = b.turnPlayer := by
  unfold summonCore at h
  simp only [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  repeat' split at h
  all_goals try (cases h; done)
  all_goals
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp [foldl_tp _ _ (fun _ _ => Board.tp_toGraveMon _ _ _)]

theorem tp_extraSummonAct {c : Ctx} {b b' : Board} {ei : Nat} {ms : List Nat}
    (h : extraSummonAct c b ei ms = .ok b') : b'.turnPlayer = b.turnPlayer := by
  unfold extraSummonAct at h
  simp only [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  repeat' split at h
  all_goals try (cases h; done)
  all_goals
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp [foldl_tp _ _ (fun _ _ => Board.tp_toGraveMon _ _ _)]

theorem tp_boardAct {c : Ctx} {b b' : Board} {a : Action} (h : boardAct c b a = .ok b') :
    b'.turnPlayer = b.turnPlayer := by
  cases a <;> simp only [boardAct] at h
  case normalSummon => exact tp_summonCore h
  case normalSet => exact tp_summonCore h
  case specialSummon => exact tp_summonCore h
  case extraSummon => exact tp_extraSummonAct h
  all_goals try (cases h; done)
  all_goals
    first
      | unfold flipSummonAct at h
      | unfold changePositionAct at h
      | unfold setSpellTrapAct at h
      | unfold declareAttack at h
      | unfold discardAct at h
    simp only [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
    repeat' split at h
    all_goals try (cases h; done)
    all_goals
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      simp

@[simp] theorem Board.tp_performBattle (c : Ctx) (b : Board) : (performBattle c b).turnPlayer = b.turnPlayer := by
  unfold performBattle
  split
  · rfl
  · dsimp only
    repeat' split
    all_goals simp

theorem tp_act {c : Ctx} {s s' : ChainState} {a : Action} (h : act c s a = .ok s') :
    s'.board.turnPlayer = s.board.turnPlayer := by
  cases a <;> simp only [act] at h
  case pass =>
    simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
    unfold passAct; split
    · split <;> simp
    · rfl
  case activateSpell => exact tp_activateSpellAct h
  case activateSet => exact tp_activateSetAct h
  case activateMonster => exact tp_activateMonsterAct h
  all_goals
    simp only [throw, throwThe, MonadExceptOf.throw] at h
    repeat' split at h
    all_goals first
      | (cases h; done)
      | (obtain ⟨b, hb, rfl⟩ := Except.map_ok h; exact tp_boardAct hb)

@[simp] theorem tp_processTriggers (c : Ctx) (s : ChainState) :
    (processTriggers c s).board.turnPlayer = s.board.turnPlayer := by
  unfold processTriggers
  split
  · rfl
  · dsimp only; split <;> rfl

@[simp] theorem Board.tp_commitAuras (b : Board) : b.commitAuras.turnPlayer = b.turnPlayer := rfl

theorem Board.tp_chooseAura {b b' : Board} {i : Nat} (h : b.chooseAura i = .ok b') :
    b'.turnPlayer = b.turnPlayer := by
  obtain ⟨r, t, rfl⟩ := Board.chooseAura_ok h
  rfl

/-- 盤面のターンプレイヤーが対戦のターンプレイヤーと一致する -/
def Game.TPOK (g : Game) : Prop := g.board.turnPlayer = g.active

theorem nextPhase_tp {g g' : Game} (hg : g.TPOK) (h : nextPhase g = .ok g') : g'.TPOK := by
  unfold nextPhase at h
  split at h
  all_goals try (simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; exact hg)
  · split at h <;> (simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; exact hg)
  · split at h
    · cases h
    · dsimp only at h
      split at h <;> (simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; simp [Game.TPOK])

/-- 1手進めても、盤面のターンプレイヤーは対戦のターンプレイヤーと一致する -/
theorem step_tp {g g' : Game} {a : Action} (hg : g.TPOK) (h : step g a = .ok g') : g'.TPOK := by
  unfold step at h
  split at h
  · cases h
  split at h
  · obtain ⟨i, b, -, hb, rfl⟩ := chooseStep_ok h
    simp only [Game.TPOK, checkResult, Board.tp_commitAuras, Board.tp_chooseAura hb]
    exact hg
  · split at h
    · split at h
      · exact nextPhase_tp hg h
      · cases h
    · cases ha : act g.ctx g.cs a <;> simp only [ha, Except.map] at h
      · cases h
      · rename_i s0
        simp only [Except.ok.injEq] at h; subst h
        have := tp_act ha
        simp only [Game.TPOK, checkResult, Game.setCs, tp_processTriggers, Board.tp_commitAuras] at this ⊢
        rw [this]; exact hg

/-- **到達可能な全状態で、盤面のターンプレイヤーは対戦のターンプレイヤーと一致する** -/
theorem reachable_turnPlayer {g : Game} (hr : Reachable g) : g.board.turnPlayer = g.active := by
  induction hr with
  | init d1 d2 e1 e2 => rfl
  | step a _ hs ih => exact step_tp ih hs

end YGO

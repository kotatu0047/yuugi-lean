import YuugiLean.Invariants

/-!
# 手順の性質

* 優先権
  * チェーンに関わらない行動（召喚・攻撃宣言など）は、空きチェーンでターンプレイヤーが
    優先権を持ち、攻撃宣言中でないときだけ行える（`act_board_needs_priority`）
  * 発動できるのは優先権を持つプレイヤーだけ（`activate_needs_priority`）
  * チェーンが空で、直前の行動がパスでなければ、優先権はターンプレイヤーにある（`reachable_prioOK`）
* パスとチェーンの解決
  * 決着がついていなければ、パスはいつでも行える（`step_pass_ok`）
  * 相手のパスを受けてパスすると、チェーンは解決されて空になり、優先権はターンプレイヤーに戻る
    （`passAct_resolves`）。その後に残るのは、解決中に起きた出来事による誘発効果だけ（`step_pass_resolves`）
  * 到達可能などの状態からでも、両者が続けてパスすればチェーンは解決される（`reachable_pass_pass`）
* 戦闘
  * ダメージ計算は `resolveBattle` のとおりに LP を減らし、破壊されたモンスターだけが
    フィールドを離れる（`performBattle_spec`。裏側守備表示の攻撃対象は表側にしてから計算する）
  * 直接攻撃では、相手の LP が攻撃力だけ減る（`performBattle_direct`）
-/

namespace YGO

/-! ## 優先権 -/

/-- パスと発動（チェーンに関わる行動） -/
def Action.isChainAct : Action → Bool
  | .pass | .activateSpell .. | .activateSet .. | .activateMonster .. => true
  | _ => false

/-- **チェーンに関わらない行動は、空きチェーンでターンプレイヤーが優先権を持ち、攻撃宣言中でないときだけ**。
行動の後も優先権はターンプレイヤーにある。 -/
theorem act_board_needs_priority {c : Ctx} {s s' : ChainState} {a : Action}
    (ha : a.isChainAct = false) (h : act c s a = .ok s') :
    s.chain = [] ∧ s.priority = c.active ∧ s.board.attack = none ∧
      s'.chain = [] ∧ s'.priority = c.active ∧ s'.passed = false := by
  cases a <;> simp only [Action.isChainAct, Bool.true_eq_false] at ha <;> simp only [act] at h
  all_goals try simp only [throw, throwThe, MonadExceptOf.throw] at h
  all_goals repeat' split at h
  all_goals try (cases h; done)
  all_goals
    obtain ⟨b, _, rfl⟩ := Except.map_ok h
    rename_i h1 h2 h3 _
    simp only [Bool.not_eq_true', List.isEmpty_eq_false_iff, Decidable.not_not, ne_eq,
      Bool.not_eq_true, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at h1 h2 h3
    exact ⟨h1, h2, h3, h1, h2, rfl⟩

theorem activateSpellAct_priority {c : Ctx} {s s' : ChainState} {hd : Nat} {args : Args}
    (h : activateSpellAct c s hd args = .ok s') : c.active = s.priority := by
  unfold activateSpellAct at h
  simp only [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  repeat' split at h
  all_goals try (cases h; done)
  rename_i hm _ _ _
  rw [← mkLink_owner hm]
  exact pushLink_priority _ _ _ _ h

theorem activateSetAct_priority {c : Ctx} {s s' : ChainState} {who : PlayerId} {z : Nat} {args : Args}
    (h : activateSetAct c s who z args = .ok s') : who = s.priority := by
  unfold activateSetAct at h
  simp only [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  repeat' split at h
  all_goals try (cases h; done)
  all_goals
    have h1 := pushLink_priority _ _ _ _ h
    rwa [mkLink_owner (by assumption)] at h1

theorem activateMonsterAct_priority {c : Ctx} {s s' : ChainState} {who : PlayerId} {z i : Nat}
    {args : Args} (h : activateMonsterAct c s who z i args = .ok s') : who = s.priority := by
  unfold activateMonsterAct at h
  simp only [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  repeat' split at h
  all_goals try (cases h; done)
  all_goals
    have h1 := pushLink_priority _ _ _ _ h
    dsimp only at h1
    rwa [mkLink_owner (by assumption)] at h1

/-- **発動できるのは優先権を持つプレイヤーだけ** -/
theorem activate_needs_priority {c : Ctx} {s s' : ChainState} :
    (∀ hd args, activateSpellAct c s hd args = .ok s' → c.active = s.priority) ∧
    (∀ who z args, activateSetAct c s who z args = .ok s' → who = s.priority) ∧
    (∀ who z i args, activateMonsterAct c s who z i args = .ok s' → who = s.priority) :=
  ⟨fun _ _ h => activateSpellAct_priority h, fun _ _ _ h => activateSetAct_priority h,
    fun _ _ _ _ h => activateMonsterAct_priority h⟩

theorem pushLink_chain_ne {s s' : ChainState} {b : Board} {l : ChainLink} (h : pushLink s b l = .ok s') :
    s'.chain ≠ [] := by
  rw [(pushLink_ok h).2]; exact List.cons_ne_nil _ _

/-- 発動の後はチェーンが空でない -/
theorem act_activate_chain {c : Ctx} {s s' : ChainState} {a : Action}
    (ha : a.isChainAct = true) (hp : a ≠ .pass) (h : act c s a = .ok s') : s'.chain ≠ [] := by
  cases a <;> simp only [Action.isChainAct, Bool.false_eq_true] at ha <;> simp only [act] at h
  case pass => exact absurd rfl hp
  all_goals
    first
      | unfold activateSpellAct at h
      | unfold activateSetAct at h
      | unfold activateMonsterAct at h
    simp only [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
    repeat' split at h
    all_goals try (cases h; done)
    all_goals exact pushLink_chain_ne h

/-- 空きチェーンで直前の行動がパスでなければ、優先権はターンプレイヤーにある -/
def ChainState.PrioOK (s : ChainState) (c : Ctx) : Prop :=
  s.chain = [] → s.passed = false → s.priority = c.active

def Game.PrioOK (g : Game) : Prop := g.chain = [] → g.passed = false → g.priority = g.active

/-- 1手の行動の後は、元の状態に関係なく成り立つ -/
theorem prioOK_act {c : Ctx} {s s' : ChainState} {a : Action} (h : act c s a = .ok s') :
    s'.PrioOK c := by
  intro hc hp
  cases hca : a.isChainAct
  · exact (act_board_needs_priority hca h).2.2.2.2.1
  · by_cases hpa : a = .pass
    · subst hpa
      simp only [act, pure, Except.pure, Except.ok.injEq] at h; subst h
      unfold passAct at hc hp ⊢
      split
      · split <;> rfl
      · rename_i h0; simp [h0] at hp
    · exact absurd hc (act_activate_chain hca hpa h)

theorem prioOK_processTriggers (c : Ctx) {s : ChainState} (hs : s.PrioOK c) :
    (processTriggers c s).PrioOK c := by
  unfold processTriggers
  split
  · exact hs
  · dsimp only
    split
    · exact hs
    · intro _ _; rfl

theorem prioOK_nextPhase {g g' : Game} (hg : g.PrioOK) (h : nextPhase g = .ok g') : g'.PrioOK := by
  unfold nextPhase at h
  split at h
  all_goals try (simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; exact hg)
  · split at h <;> (simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; exact hg)
  · split at h
    · cases h
    · dsimp only at h
      split at h <;> (simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; intro _ _; rfl)

theorem step_prioOK {g g' : Game} {a : Action} (hg : g.PrioOK) (h : step g a = .ok g') : g'.PrioOK := by
  unfold step at h
  split at h
  · cases h
  · split at h
    · split at h
      · exact prioOK_nextPhase hg h
      · cases h
    · cases ha : act g.ctx g.cs a <;> simp only [ha, Except.map] at h
      · cases h
      · rename_i s0
        simp only [Except.ok.injEq] at h; subst h
        have h0 := prioOK_act (s := g.cs) ha
        exact prioOK_processTriggers g.ctx (s := { s0 with board := s0.board.commitAuras }) h0

/-- **到達可能な全状態で、チェーンが空で直前の行動がパスでなければ、優先権はターンプレイヤーにある**。
相手が空きチェーンで発動できるのは、ターンプレイヤーがパスした直後だけ。 -/
theorem reachable_prioOK {g : Game} (hr : Reachable g) : g.PrioOK := by
  induction hr with
  | init d1 d2 e1 e2 => intro _ _; rfl
  | step a _ hs ih => exact step_prioOK ih hs

/-! ## パスとチェーンの解決 -/

/-- **パスはいつでも行える**（決着がついていなければ） -/
theorem step_pass_ok {g : Game} (hn : g.result = none) : ∃ g', step g .pass = .ok g' := by
  simp [step, hn, Action.isNextPhase, act, Except.map, pure, Except.pure]

/-- **相手のパスを受けてパスすると、チェーンは解決されて空になり、優先権はターンプレイヤーに戻る**。
攻撃宣言中でチェーンが空なら、ダメージ計算を行う。 -/
theorem passAct_resolves (c : Ctx) {s : ChainState} (hp : s.passed = true) :
    (passAct c s).chain = [] ∧ (passAct c s).priority = c.active ∧ (passAct c s).passed = false ∧
      (passAct c s).board =
        if s.chain.isEmpty then performBattle c s.board else resolveChain c s.board false s.chain := by
  unfold passAct
  simp only [hp, ite_true]
  split <;> simp_all

/-- 誘発効果だけからなるチェーンの性質：記録された出来事 `hs` のいずれかに対応する誘発効果 -/
def TriggeredBy (hs : List Happened) (ch : List ChainLink) : Prop :=
  ∀ l ∈ ch, ∃ h ∈ hs, l ∈ triggeredLinks h

theorem processTriggers_chain (c : Ctx) {s : ChainState} (hc : s.chain = []) :
    TriggeredBy s.board.log (processTriggers c s).chain := by
  unfold processTriggers
  simp only [hc, List.isEmpty_nil, Bool.not_true, Bool.false_eq_true, ite_false]
  split
  · intro l hl; simp at hl
  · intro l hl
    simp only [List.mem_reverse, List.mem_append, List.mem_filter, List.mem_flatMap] at hl
    rcases hl with ⟨hl, _⟩ | ⟨hl, _⟩ <;> exact hl

/-- **両者が続けてパスすると、チェーンは解決される**。1手後のチェーンに残るのは、解決中に起きた出来事
（記録 `log`）による誘発効果だけ。誘発効果がなければチェーンは空になる。 -/
theorem step_pass_resolves {g g' : Game} (hp : g.passed = true) (h : step g .pass = .ok g') :
    TriggeredBy (passAct g.ctx g.cs).board.log g'.chain := by
  unfold step at h
  split at h
  · cases h
  · simp only [Action.isNextPhase, Bool.false_eq_true, ite_false, act, pure, Except.pure,
      Except.map, Except.ok.injEq] at h
    subst h
    exact processTriggers_chain g.ctx (passAct_resolves g.ctx hp).1

/-- チェーンが空のときは、出来事の記録も空（誘発効果はチェーンが空になった時点で処理される） -/
def Game.LogOK (g : Game) : Prop := g.chain = [] → g.board.log = []

theorem Board.log_modify (b : Board) (w : PlayerId) (f : Player → Player) : (b.modify w f).log = b.log := by
  cases w <;> rfl

theorem Board.log_set (b : Board) (w : PlayerId) (p : Player) : (b.set w p).log = b.log := by
  cases w <;> rfl

theorem logOK_processTriggers (c : Ctx) (s : ChainState) :
    (processTriggers c s).chain = [] → (processTriggers c s).board.log = [] := by
  unfold processTriggers
  split
  · rename_i hc; intro h; simp [h] at hc
  · dsimp only
    split <;> intro _ <;> rfl

theorem step_logOK {g g' : Game} {a : Action} (hg : g.LogOK) (h : step g a = .ok g') : g'.LogOK := by
  unfold step at h
  split at h
  · cases h
  · split at h
    · split at h
      · unfold nextPhase at h
        split at h
        all_goals try (simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; exact hg)
        · split at h <;> (simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; exact hg)
        · split at h
          · cases h
          · dsimp only at h
            split at h
            · simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
              intro hc; simp only [Board.log_modify]; exact hg hc
            · simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
              intro hc; simp only [Board.log_set, Board.log_modify]; exact hg hc
      · cases h
    · cases ha : act g.ctx g.cs a <;> simp only [ha, Except.map] at h
      · cases h
      · rename_i s0
        simp only [Except.ok.injEq] at h; subst h
        exact logOK_processTriggers g.ctx _

theorem reachable_logOK {g : Game} (hr : Reachable g) : g.LogOK := by
  induction hr with
  | init d1 d2 e1 e2 => intro _; rfl
  | step a _ hs ih => exact step_logOK ih hs

/-- **到達可能などの状態からでも、両者が続けてパスすれば、その時点のチェーンは解決される**。
1回目のパスではチェーンも勝敗も変わらず、2回目のパスの後に残るのは解決中に誘発した効果だけ。 -/
theorem reachable_pass_pass {g : Game} (hr : Reachable g) (hn : g.result = none) (hp : g.passed = false) :
    ∃ g1 g2, step g .pass = .ok g1 ∧ step g1 .pass = .ok g2 ∧ g1.chain = g.chain ∧ g1.result = none ∧
      TriggeredBy (passAct g1.ctx g1.cs).board.log g2.chain := by
  have hlp := reachable_LPOK hr hn
  have hlog := reachable_logOK hr
  -- 1回目のパス：優先権が相手に移るだけ（チェーンが空なら記録も空なので誘発効果は起きない）
  have hpt : processTriggers g.ctx { passAct g.ctx g.cs with board := (passAct g.ctx g.cs).board.commitAuras } =
      { g.cs with priority := g.priority.other, passed := true,
                  board := if g.chain = [] then { g.board.commitAuras with log := [] }
                           else g.board.commitAuras } := by
    simp only [passAct, Game.cs, hp, Bool.false_eq_true, ite_false]
    unfold processTriggers
    by_cases hc : g.chain = []
    · have : g.board.commitAuras.log = [] := hlog hc
      simp [hc, this]
    · simp [hc]
  let g1 := checkResult (g.setCs (processTriggers g.ctx
    { passAct g.ctx g.cs with board := (passAct g.ctx g.cs).board.commitAuras }))
  have h1 : step g .pass = .ok g1 := by
    simp [step, hn, Action.isNextPhase, act, Except.map, pure, Except.pure, g1]
  have hc1 : g1.chain = g.chain := by simp only [g1, checkResult, Game.setCs]; rw [hpt]; rfl
  have hp1 : g1.passed = true := by simp only [g1, checkResult, Game.setCs]; rw [hpt]
  have hn1 : g1.result = none := by
    simp only [g1, checkResult, Game.setCs]; rw [hpt]
    have : ∀ b : Board, b.p1.lp = g.board.p1.lp → b.p2.lp = g.board.p2.lp →
        (if b.p1.lp = 0 ∧ b.p2.lp = 0 then some Outcome.draw else if b.p1.lp = 0 then some (.win .two)
          else if b.p2.lp = 0 then some (.win .one) else none) = none := by
      intro b e1 e2; rw [e1, e2]; simp only [Nat.pos_iff_ne_zero.mp hlp.1, Nat.pos_iff_ne_zero.mp hlp.2]
      simp
    simp only [hn]
    apply this <;> split <;> rfl
  obtain ⟨g2, h2⟩ := step_pass_ok hn1
  exact ⟨g1, g2, h1, h2, hc1, hn1, step_pass_resolves hp1 h2⟩

/-! ## 戦闘 -/

theorem mem_uids_eraseIdx {l : List FieldMonster} {i : Nat} {m : FieldMonster} {x : Nat}
    (hn : (l.map (·.uid)).Nodup) (hm : l[i]? = some m) :
    x ∈ (l.eraseIdx i).map (·.uid) ↔ x ∈ l.map (·.uid) ∧ x ≠ m.uid := by
  simp only [List.mem_map, List.mem_eraseIdx_iff_getElem?]
  constructor
  · rintro ⟨y, ⟨j, hj, hy⟩, rfl⟩
    refine ⟨⟨y, List.mem_of_getElem? hy, rfl⟩, fun he => hj ?_⟩
    have hi : i < (l.map (·.uid)).length := by
      simp only [List.length_map]; exact (List.getElem?_eq_some_iff.mp hm).1
    exact ((hn.getElem?_inj hi).mp (by simp [hm, hy, he])).symm
  · rintro ⟨⟨y, hy, rfl⟩, hne⟩
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hy
    exact ⟨y, ⟨j, fun he => hne (by subst he; rw [hm] at hj; cases hj; rfl), hj⟩, rfl⟩


theorem Board.findMonIdx_some {b : Board} {u : Nat} {w : PlayerId} {i : Nat}
    (h : b.findMonIdx u = some (w, i)) : ∃ m, (b.get w).monsters[i]? = some m ∧ m.uid = u := by
  unfold Board.findMonIdx at h
  split at h
  · rename_i j hj
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    obtain ⟨hl, hp, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hj
    exact ⟨_, List.getElem?_eq_getElem hl, by simpa using hp⟩
  · rename_i hj
    cases hk : b.p2.monsters.findIdx? (·.uid == u) with
    | none => simp [hk] at h
    | some k =>
      simp only [hk, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
      obtain ⟨hl, hp, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hk
      exact ⟨_, List.getElem?_eq_getElem hl, by simpa using hp⟩

theorem Board.findMonIdx_none {b : Board} {u : Nat} (h : b.findMonIdx u = none) (v : PlayerId) :
    u ∉ b.uidsOf v := by
  unfold Board.findMonIdx at h
  split at h
  · cases h
  · rename_i hj
    cases hk : b.p2.monsters.findIdx? (·.uid == u) with
    | some k => simp [hk] at h
    | none =>
      intro hu
      simp only [Board.uidsOf, List.mem_map] at hu
      obtain ⟨m, hm, rfl⟩ := hu
      cases v
      · have := List.findIdx?_eq_none_iff.mp hj m hm; simp at this
      · have := List.findIdx?_eq_none_iff.mp hk m hm; simp at this

theorem Board.UidOK.disjoint {b : Board} (h : b.UidOK) {v w : PlayerId} (hv : v ≠ w) {x : Nat}
    (hx : x ∈ b.uidsOf w) : x ∉ b.uidsOf v := by
  have hn := (List.nodup_append.mp h.1).2.2
  intro hx'
  cases v <;> cases w
  · exact hv rfl
  · exact hn x hx' x hx rfl
  · exact hn x hx x hx' rfl
  · exact hv rfl

theorem Board.UidOK.nodupOf {b : Board} (h : b.UidOK) (v : PlayerId) : (b.uidsOf v).Nodup := by
  have := List.nodup_append.mp h.1
  cases v
  · exact this.1
  · exact this.2.1

theorem Board.uidsOf_modify_eq (b : Board) (w : PlayerId) (f : Player → Player)
    (hf : ∀ p, (f p).monsters = p.monsters) (v : PlayerId) : (b.modify w f).uidsOf v = b.uidsOf v := by
  by_cases hv : v = w
  · subst hv; simp only [Board.uidsOf, Board.get_modify_same, hf]
  · simp only [Board.uidsOf, Board.get_modify_other _ _ _ _ hv]

/-- 取り除いたモンスター以外は、フィールドに残る -/
theorem Board.mem_uidsOf_detach {b b' : Board} {u : Nat} {w : PlayerId} {m : FieldMonster}
    (hu : b.UidOK) (h : b.detach u = some (b', w, m)) (v : PlayerId) (x : Nat) :
    x ∈ b'.uidsOf v ↔ x ∈ b.uidsOf v ∧ x ≠ u := by
  unfold Board.detach at h
  cases hf : b.findMonIdx u with
  | none => simp [hf] at h
  | some wi =>
    obtain ⟨w0, i⟩ := wi
    obtain ⟨m0, hm0, hu0⟩ := Board.findMonIdx_some hf
    simp only [hf, hm0, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq,
      Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    rw [Board.uidsOf_modify_eq _ _ _ ?h1, Board.uidsOf_modify_eq _ _ _ ?h2]
    case h1 | h2 => intro; rfl
    by_cases hv : v = w0
    · subst hv
      simp only [Board.uidsOf, Board.get_modify_same]
      rw [← hu0]
      exact mem_uids_eraseIdx (hu.nodupOf v) hm0
    · simp only [Board.uidsOf, Board.get_modify_other _ _ _ _ hv]
      constructor
      · intro hx; refine ⟨hx, fun he => ?_⟩
        subst he
        exact hu.disjoint hv (by rw [← hu0]; exact List.mem_map_of_mem (List.mem_of_getElem? hm0)) hx
      · exact fun h => h.1


theorem Board.detach_none {b : Board} {u : Nat} (h : b.detach u = none) (v : PlayerId) : u ∉ b.uidsOf v := by
  cases hf : b.findMonIdx u with
  | none => exact Board.findMonIdx_none hf v
  | some wi =>
    obtain ⟨w0, i⟩ := wi
    obtain ⟨m0, hm0, _⟩ := Board.findMonIdx_some hf
    unfold Board.detach at h
    simp [hf, hm0] at h

/-- **墓地へ送ったモンスターだけがフィールドから離れる** -/
theorem Board.mem_uidsOf_toGraveMon {b : Board} (hu : b.UidOK) (u : Nat) (c : LeaveCause) (v : PlayerId)
    (x : Nat) : x ∈ (b.toGraveMon u c).uidsOf v ↔ x ∈ b.uidsOf v ∧ x ≠ u := by
  unfold Board.toGraveMon
  split
  · rename_i hd
    exact ⟨fun h => ⟨h, fun he => Board.detach_none hd v (he ▸ h)⟩, fun h => h.1⟩
  · rename_i b' w m hd
    rw [← Board.mem_uidsOf_detach hu hd v x]
    dsimp only
    split
    · show x ∈ (b'.modify w _).uidsOf v ↔ _
      rw [Board.uidsOf_modify_eq _ _ _ ?h1]
      case h1 => intro; rfl
    · rw [Board.uidsOf_modify_eq _ _ _ ?h1, Board.uidsOf_modify_eq _ _ _ ?h2]
      case h1 | h2 => intro; rfl
      show x ∈ (b'.modify w _).uidsOf v ↔ _
      rw [Board.uidsOf_modify_eq _ _ _ ?h3]
      case h3 => intro; rfl


@[simp] theorem Board.get_with_attack (b : Board) (x : Option AttackDecl) (v : PlayerId) :
    ({ b with attack := x } : Board).get v = b.get v := by cases v <;> rfl

theorem Board.atkOf_with_attack (b : Board) (x : Option AttackDecl) (v : PlayerId) (m : FieldMonster) :
    ({ b with attack := x } : Board).atkOf v m = b.atkOf v m := rfl

theorem Board.updMon_id (b : Board) (w : PlayerId) (u : Nat) : b.updMon w u (fun x => x) = b := by
  cases w <;> simp [Board.updMon, Board.modify, Board.set, Board.get]

theorem Board.attack_modify (b : Board) (w : PlayerId) (f : Player → Player) : (b.modify w f).attack = b.attack := by
  cases w <;> rfl

theorem Board.attack_toGraveMon (b : Board) (u : Nat) (c : LeaveCause) : (b.toGraveMon u c).attack = b.attack := by
  unfold Board.toGraveMon
  split
  · rfl
  · rename_i b' w m hd
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
        dsimp only
        split <;> simp only [Board.attack_modify]

theorem Board.get_eq_of {B Z : Board} (h1 : B.p1 = Z.p1) (h2 : B.p2 = Z.p2) (v : PlayerId) :
    B.get v = Z.get v := by cases v <;> assumption

theorem Board.uidsOf_eq_of {B Z : Board} (h1 : B.p1 = Z.p1) (h2 : B.p2 = Z.p2) (v : PlayerId) :
    B.uidsOf v = Z.uidsOf v := by simp only [Board.uidsOf, Board.get_eq_of h1 h2]

theorem resolveBattle_def_indep (a : Nat) {pos : Position} (hp : pos ≠ .attack) (x x' y : Nat) :
    resolveBattle a pos x y = resolveBattle a pos x' y := by
  cases pos
  · exact absurd rfl hp
  all_goals rfl

theorem Board.uidsOf_updMon (b : Board) (w : PlayerId) (u : Nat) (f : FieldMonster → FieldMonster)
    (hf : ∀ x, (f x).uid = x.uid) (v : PlayerId) : (b.updMon w u f).uidsOf v = b.uidsOf v := by
  by_cases hv : v = w
  · subst hv
    simp only [Board.updMon, Board.uidsOf, Board.get_modify_same, List.map_map]
    congr 1; funext m; simp only [Function.comp]; split <;> simp [hf]
  · simp only [Board.updMon, Board.uidsOf, Board.get_modify_other _ _ _ _ hv]

theorem Board.lp_updMon (b : Board) (w : PlayerId) (u : Nat) (f : FieldMonster → FieldMonster)
    (v : PlayerId) : ((b.updMon w u f).get v).lp = (b.get v).lp := by
  by_cases hv : v = w
  · subst hv; simp only [Board.updMon, Board.get_modify_same]
  · simp only [Board.updMon, Board.get_modify_other _ _ _ _ hv]

theorem Board.attack_updMon (b : Board) (w : PlayerId) (u : Nat) (f : FieldMonster → FieldMonster) :
    (b.updMon w u f).attack = b.attack := Board.attack_modify _ _ _

/-- ダメージを与えた後の盤面 B1 から、攻撃モンスター・攻撃対象を破壊する処理 -/
theorem battle_finish {b B1 : Board} {me : PlayerId} {au tu : Nat} {R : BattleResult} (hu : b.UidOK)
    (hB1 : B1.UidOK) (hl1 : (B1.get me).lp = (b.get me).lp - R.dmgToAttacker)
    (hl2 : (B1.get me.other).lp = (b.get me.other).lp - R.dmgToDefender)
    (hu1 : ∀ v, B1.uidsOf v = b.uidsOf v) (ha1 : B1.attack = none)
    (hau : au ∈ b.uidsOf me) (htu : tu ∈ b.uidsOf me.other) :
    let B2 := if R.attackerDestroyed = true then B1.toGraveMon au .battle else B1
    let B := if R.defenderDestroyed = true then B2.toGraveMon tu .battle else B2
    (B.get me).lp = (b.get me).lp - R.dmgToAttacker ∧
    (B.get me.other).lp = (b.get me.other).lp - R.dmgToDefender ∧
    (au ∈ B.uidsOf me ↔ R.attackerDestroyed = false) ∧
    (tu ∈ B.uidsOf me.other ↔ R.defenderDestroyed = false) ∧
    B.attack = none := by
  intro B2 B
  have hat : au ≠ tu := fun he => hu.disjoint (PlayerId.other_ne me) hau (he ▸ htu)
  have hlp : ∀ (B : Board) u v, ((B.toGraveMon u .battle).get v).lp = (B.get v).lp :=
    fun B u v => (Board.frame_toGraveMon B u .battle v).1
  have hm : ∀ {B : Board}, B.UidOK → ∀ u v x, x ∈ (B.toGraveMon u .battle).uidsOf v ↔ x ∈ B.uidsOf v ∧ x ≠ u :=
    fun h u v x => Board.mem_uidsOf_toGraveMon h u .battle v x
  have hau' := hu1 me ▸ hau
  have htu' := hu1 me.other ▸ htu
  cases hA : R.attackerDestroyed <;> cases hD : R.defenderDestroyed <;>
    simp only [B, B2, hlp, hl1, hl2, hm hB1, hm (hB1.toGraveMon _ _), Board.attack_toGraveMon, ha1, hA, hD,
      hau', htu', ne_eq, hat, Ne.symm hat, not_true_eq_false, not_false_eq_true, and_true, and_false,
      ite_true, ite_false, Bool.false_eq_true, true_and] <;> trivial

/-- **ダメージ計算は resolveBattle のとおりに行われる**：攻撃モンスターと攻撃対象がフィールドに残っていれば、
両者の LP は resolveBattle の戦闘ダメージだけ減り、破壊されたモンスターだけがフィールドを離れる。
裏側守備表示の攻撃対象は、表側守備表示にしてからダメージ計算を行う。 -/
theorem performBattle_spec (c : Ctx) {b : Board} (hu : b.UidOK) {au tu : Nat} {a d : FieldMonster}
    (hb : b.attack = some ⟨au, some tu⟩)
    (ha : (b.get c.active).monsters.find? (·.uid == au) = some a) (hpos : a.pos = .attack)
    (hd : (b.get c.active.other).monsters.find? (·.uid == tu) = some d) :
    let pos := if d.pos = .faceDownDefense then .faceUpDefense else d.pos
    let r := resolveBattle (b.atkOf c.active a) pos (b.atkOf c.active.other d) d.card.dfs
    let b' := performBattle c b
    (b'.get c.active).lp = (b.get c.active).lp - r.dmgToAttacker ∧
    (b'.get c.active.other).lp = (b.get c.active.other).lp - r.dmgToDefender ∧
    (au ∈ b'.uidsOf c.active ↔ r.attackerDestroyed = false) ∧
    (tu ∈ b'.uidsOf c.active.other ↔ r.defenderDestroyed = false) ∧
    b'.attack = none := by
  intro pos
  have hne : c.active.other ≠ c.active := PlayerId.other_ne _
  -- 攻撃モンスターと攻撃対象はフィールドにいる
  have hau : au ∈ b.uidsOf c.active := by
    have := List.find?_some ha; simp at this
    exact List.mem_map.mpr ⟨a, List.mem_of_find?_eq_some ha, this⟩
  have htu : tu ∈ b.uidsOf c.active.other := by
    have := List.find?_some hd; simp at this
    exact List.mem_map.mpr ⟨d, List.mem_of_find?_eq_some hd, this⟩
  have ha' : a.uid = au := by have := List.find?_some ha; simpa using this
  by_cases hdf : d.pos = .faceDownDefense
  · simp only [pos, hdf, ite_true]
    have e : ∀ v m, ({ b with attack := none } : Board).atkOf v m = b.atkOf v m := fun _ _ => rfl
    simp only [performBattle, hb, Board.get_with_attack, ha, hpos, ne_eq, not_true_eq_false, ite_false,
      hd, hdf, ite_true, e]
    rw [resolveBattle_def_indep _ (by decide) _ (b.atkOf c.active.other d)]
    generalize resolveBattle (b.atkOf c.active a) Position.faceUpDefense (b.atkOf c.active.other d) d.card.dfs = R
    -- 裏側守備表示の攻撃対象を表側にした盤面
    generalize hZ : Board.updMon _ c.active.other tu _ = Z
    have hZu : Z.UidOK := by
      rw [← hZ]; exact ((hu.with_attack none).with_clock _).updMon _ _ _ (fun _ => rfl)
    have hZl : ∀ v, (Z.get v).lp = (b.get v).lp := by
      intro v; rw [← hZ, Board.lp_updMon]; cases v <;> rfl
    have hZi : ∀ v, Z.uidsOf v = b.uidsOf v := by
      intro v; rw [← hZ, Board.uidsOf_updMon _ _ _ _ ?hf]
      · cases v <;> rfl
      · intro; rfl
    have hZa : Z.attack = none := by rw [← hZ, Board.attack_updMon]
    clear hZ
    generalize hY : ({ Z with log := Z.log ++ [_] } : Board) = Y
    have hYu : Y.UidOK := by rw [← hY]; exact hZu.with_log _
    have hYg : ∀ v, Y.get v = Z.get v := by intro v; rw [← hY]; cases v <;> rfl
    have hYa : Y.attack = none := by rw [← hY]; exact hZa
    clear hY
    generalize hX : Board.modify (Board.modify Y c.active (fun x => x.damage R.dmgToAttacker)) c.active.other
      (fun x => x.damage R.dmgToDefender) = B1
    have hB1 : B1.UidOK := by
      rw [← hX]; refine (hYu.modify_eq ?_).modify_eq ?_ <;> rfl
    have hl1 : (B1.get c.active).lp = (b.get c.active).lp - R.dmgToAttacker := by
      rw [← hX, Board.get_modify_other _ _ _ _ hne.symm, Board.get_modify_same, hYg]
      show (Z.get c.active).lp - _ = _
      rw [hZl]
    have hl2 : (B1.get c.active.other).lp = (b.get c.active.other).lp - R.dmgToDefender := by
      rw [← hX, Board.get_modify_same, Board.get_modify_other _ _ _ _ hne, hYg]
      show (Z.get c.active.other).lp - _ = _
      rw [hZl]
    have hu1 : ∀ v, B1.uidsOf v = b.uidsOf v := by
      intro v
      rw [← hX, Board.uidsOf_modify_eq _ _ _ ?h1, Board.uidsOf_modify_eq _ _ _ ?h2]
      case h1 | h2 => intro; rfl
      simp only [Board.uidsOf, hYg]; exact hZi v
    have ha1 : B1.attack = none := by
      rw [← hX, Board.attack_modify, Board.attack_modify]; exact hYa
    rw [ha'] at *
    exact battle_finish hu hB1 hl1 hl2 hu1 ha1 hau htu
  · simp only [pos, hdf, ite_false]
    have e : ∀ v m, ({ b with attack := none } : Board).atkOf v m = b.atkOf v m := fun _ _ => rfl
    simp only [performBattle, hb, Board.get_with_attack, ha, hpos, ne_eq, not_true_eq_false, ite_false,
      hd, hdf, Board.updMon_id, e]
    rw [ha']
    have hB := hu.with_attack none
    have hBa : ({ b with attack := none } : Board).attack = none := rfl
    have hB0 : ∀ v, ({ b with attack := none } : Board).get v = b.get v := fun v => Board.get_with_attack b none v
    generalize ({ b with attack := none } : Board) = B0 at *
    generalize resolveBattle (b.atkOf c.active a) d.pos (b.atkOf c.active.other d) d.card.dfs = R
    -- ダメージを与えた後の盤面
    have hB1 := (hB.modify_eq (w := c.active) (f := fun x => x.damage R.dmgToAttacker) rfl).modify_eq
      (w := c.active.other) (f := fun x => x.damage R.dmgToDefender) rfl
    have hl1 : (((B0.modify c.active fun x => x.damage R.dmgToAttacker).modify c.active.other fun x =>
        x.damage R.dmgToDefender).get c.active).lp = (b.get c.active).lp - R.dmgToAttacker := by
      rw [Board.get_modify_other _ _ _ _ hne.symm, Board.get_modify_same, hB0]; rfl
    have hl2 : (((B0.modify c.active fun x => x.damage R.dmgToAttacker).modify c.active.other fun x =>
        x.damage R.dmgToDefender).get c.active.other).lp = (b.get c.active.other).lp - R.dmgToDefender := by
      rw [Board.get_modify_same, Board.get_modify_other _ _ _ _ hne, hB0]; rfl
    have hu1 : ∀ v, ((B0.modify c.active fun x => x.damage R.dmgToAttacker).modify c.active.other fun x =>
        x.damage R.dmgToDefender).uidsOf v = b.uidsOf v := by
      intro v
      rw [Board.uidsOf_modify_eq _ _ _ ?h1, Board.uidsOf_modify_eq _ _ _ ?h2]
      case h1 | h2 => intro; rfl
      simp only [Board.uidsOf, hB0]
    have ha1 : ((B0.modify c.active fun x => x.damage R.dmgToAttacker).modify c.active.other fun x =>
        x.damage R.dmgToDefender).attack = B0.attack := by
      rw [Board.attack_modify, Board.attack_modify]
    generalize ((B0.modify c.active fun x => x.damage R.dmgToAttacker).modify c.active.other fun x =>
        x.damage R.dmgToDefender) = B1 at *
    exact battle_finish hu hB1 hl1 hl2 hu1 (ha1.trans hBa) hau htu

/-- **直接攻撃では、相手の LP が攻撃モンスターの攻撃力だけ減る**（相手フィールドにモンスターがいなければ） -/
theorem performBattle_direct (c : Ctx) {b : Board} {au : Nat} {a : FieldMonster}
    (hb : b.attack = some ⟨au, none⟩)
    (ha : (b.get c.active).monsters.find? (·.uid == au) = some a) (hpos : a.pos = .attack)
    (hopp : (b.get c.active.other).monsters = []) :
    ((performBattle c b).get c.active.other).lp = (b.get c.active.other).lp - b.atkOf c.active a ∧
    ((performBattle c b).get c.active).lp = (b.get c.active).lp ∧
    (performBattle c b).attack = none := by
  have hne : c.active.other ≠ c.active := PlayerId.other_ne _
  simp only [performBattle, hb, Board.get_with_attack, ha, hpos, ne_eq, not_true_eq_false, ite_false, hopp,
    List.isEmpty_nil, ite_true]
  refine ⟨?_, ?_, ?_⟩
  · rw [Board.get_modify_same, Board.get_with_attack]; rfl
  · rw [Board.get_modify_other _ _ _ _ hne.symm, Board.get_with_attack]
  · rw [Board.attack_modify]

end YGO

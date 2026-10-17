import YuugiLean.Settle

/-!
# 判定は適用の時刻の大小関係だけで決まる

永続効果の有効・無効の判定（`settleOnce`・`returnCands`・`awaitingChoice`）は、適用の時刻（`AuraSrc.since`）を
「どちらが先に適用されたか」の比較にしか使わない。有効に戻すときの新しい時刻（`newestTime`）も、どのカードより
新しいことだけが効く。

そこで、2つの状態が「時刻以外は同じで、時刻の大小関係も同じ」（`OrderPairs`）なら、判定の進み方も止まり方も
同じになる（`settleOnce_pairs`・`awaitingChoice_pairs`・`returnCands_pairs`）。時計（`clock`）の値も効かない。
-/

namespace YGO

/-- 対応するカードの組の並び。組の2枚は時刻以外が同じで、どの2組についても時刻の大小関係が同じ。
`P.map (·.1)` と `P.map (·.2)` が比べる2つの状態。 -/
def OrderPairs (P : List (AuraSrc × AuraSrc)) : Prop :=
  (∀ p ∈ P, p.2 = { p.1 with since := p.2.since }) ∧
  (∀ p ∈ P, ∀ q ∈ P, (p.1.since < q.1.since ↔ p.2.since < q.2.since))

namespace OrderPairs

theorem any_congr' {α : Type} {L : List α} {f g : α → Bool} (h : ∀ x ∈ L, f x = g x) : L.any f = L.any g := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    simp only [List.any_cons, h a List.mem_cons_self, ih fun x hx => h x (List.mem_cons_of_mem _ hx)]

theorem filter_congr' {α : Type} {L : List α} {f g : α → Bool} (h : ∀ x ∈ L, f x = g x) :
    L.filter f = L.filter g := List.filter_congr h

theorem findIdx?_congr' {α : Type} {L : List α} {f g : α → Bool} (h : ∀ x ∈ L, f x = g x) :
    L.findIdx? f = L.findIdx? g := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    simp only [List.findIdx?_cons, h a List.mem_cons_self, ih fun x hx => h x (List.mem_cons_of_mem _ hx)]

theorem opt_any {α : Type} {P : List α} {j : Nat} {f g : α → Bool} (h : ∀ x ∈ P, f x = g x) :
    P[j]?.any f = P[j]?.any g := by
  cases hj : P[j]? with
  | none => rfl
  | some x => simpa using h x (List.mem_of_getElem? hj)

theorem mem_modify {α : Type} {L : List α} {i : Nat} {f : α → α} {x : α} (hx : x ∈ L.modify i f) :
    x ∈ L ∨ ∃ y ∈ L, x = f y := by
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hx
  by_cases hij : i = j
  · subst hij
    rw [List.getElem?_modify_eq] at hj
    obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.mp hj
    exact .inr ⟨y, List.mem_of_getElem? hy, rfl⟩
  · rw [List.getElem?_modify_ne _ _ hij] at hj
    exact .inl (List.mem_of_getElem? hj)

theorem map_modify {α β : Type} (L : List α) (i : Nat) (f : α → α) (g : α → β) (f' : β → β)
    (h : ∀ x, g (f x) = f' (g x)) : (L.modify i f).map g = (L.map g).modify i f' := by
  apply List.ext_getElem?
  intro j
  by_cases hij : i = j
  · subst hij
    simp only [List.getElem?_map, List.getElem?_modify_eq]
    cases L[i]? <;> simp [h]
  · simp only [List.getElem?_map, List.getElem?_modify_ne _ _ hij]

/-- 位置ごとの性質が同じなら、有効に戻せるカードの位置も同じ -/
theorem returnCands_congr {L1 L2 : List AuraSrc} {tp : PlayerId} (hl : L1.length = L2.length)
    (h1 : ∀ j : Nat, L1[j]?.any (fun s => !s.on && !YGO.beatenIn L1 s) =
      L2[j]?.any (fun s => !s.on && !YGO.beatenIn L2 s))
    (h2 : ∀ j : Nat, L1[j]?.any AuraSrc.inert = L2[j]?.any AuraSrc.inert)
    (h3 : ∀ j : Nat, L1[j]?.any (fun s : AuraSrc => s.who == tp) = L2[j]?.any (fun s : AuraSrc => s.who == tp)) :
    YGO.returnCands L1 tp = YGO.returnCands L2 tp := by
  unfold YGO.returnCands
  simp only [hl, h1, h2, h3]

variable {P : List (AuraSrc × AuraSrc)} (H : OrderPairs P)
include H

theorem fields {p : AuraSrc × AuraSrc} (hp : p ∈ P) :
    p.2.who = p.1.who ∧ p.2.kind = p.1.kind ∧ p.2.key = p.1.key ∧ p.2.on = p.1.on ∧ p.2.auras = p.1.auras := by
  have h := H.1 p hp
  obtain ⟨a, b⟩ := p
  cases a; cases b
  simp only [AuraSrc.mk.injEq] at h
  simp [h]

theorem negates {p q : AuraSrc × AuraSrc} (hp : p ∈ P) (hq : q ∈ P) : p.2.negates q.2 = p.1.negates q.1 := by
  obtain ⟨h1, h2, h3, -, h5⟩ := H.fields hp
  obtain ⟨g1, g2, g3, -, g5⟩ := H.fields hq
  simp only [AuraSrc.negates, h1, h3, h5, g1, g2, g3]

theorem beats {p q : AuraSrc × AuraSrc} (hp : p ∈ P) (hq : q ∈ P) : p.2.beats q.2 = p.1.beats q.1 := by
  simp only [AuraSrc.beats, H.negates hp hq, H.negates hq hp, (H.2 q hq p hp).symm]

theorem beatenIn {p : AuraSrc × AuraSrc} (hp : p ∈ P) :
    YGO.beatenIn (P.map (·.2)) p.2 = YGO.beatenIn (P.map (·.1)) p.1 := by
  simp only [YGO.beatenIn, List.any_map]
  exact any_congr' fun q hq => by simp [(H.fields hq).2.2.2.1, H.beats hq hp]

theorem on {p : AuraSrc × AuraSrc} (hp : p ∈ P) : p.2.on = p.1.on := (H.fields hp).2.2.2.1

theorem inert {p : AuraSrc × AuraSrc} (hp : p ∈ P) : p.2.inert = p.1.inert := by
  simp [AuraSrc.inert, (H.fields hp).2.2.2.2]

theorem who {p : AuraSrc × AuraSrc} (hp : p ∈ P) : p.2.who = p.1.who := (H.fields hp).1

omit H in
theorem idx {j : Nat} {f1 f2 : AuraSrc → Bool} (h : ∀ p ∈ P, f2 p.2 = f1 p.1) :
    (P.map (·.2))[j]?.any f2 = (P.map (·.1))[j]?.any f1 := by
  rw [List.getElem?_map, List.getElem?_map]
  cases hj : P[j]? with
  | none => rfl
  | some p => simpa using h p (List.mem_of_getElem? hj)

/-- 有効に戻せるカードの位置は同じ -/
theorem returnCands (tp : PlayerId) : YGO.returnCands (P.map (·.2)) tp = YGO.returnCands (P.map (·.1)) tp :=
  returnCands_congr (by simp) (fun _ => idx fun p hp => by simp [H.on hp, H.beatenIn hp])
    (fun _ => idx fun p hp => H.inert hp) (fun _ => idx fun p hp => by simp [H.who hp])

theorem anyBeaten : (P.map (·.2)).any (fun s => s.on && YGO.beatenIn (P.map (·.2)) s) =
    (P.map (·.1)).any (fun s => s.on && YGO.beatenIn (P.map (·.1)) s) := by
  simp only [List.any_map]
  exact any_congr' fun p hp => by simp [H.on hp, H.beatenIn hp]

theorem findBeaten : (P.map (·.2)).findIdx? (fun s => s.on && YGO.beatenIn (P.map (·.2)) s) =
    (P.map (·.1)).findIdx? (fun s => s.on && YGO.beatenIn (P.map (·.1)) s) := by
  simp only [List.findIdx?_map]
  exact findIdx?_congr' fun p hp => by simp [H.on hp, H.beatenIn hp]

/-- 選択待ちかどうか（と選ぶプレイヤー）は同じ -/
theorem awaitingChoice (tp : PlayerId) :
    YGO.awaitingChoice (P.map (·.2)) tp = YGO.awaitingChoice (P.map (·.1)) tp := by
  unfold YGO.awaitingChoice
  rw [H.anyBeaten, H.returnCands]
  split
  · rfl
  · split
    · rename_i i _ _ _
      rw [List.getElem?_map, List.getElem?_map]
      cases hj : P[i]? with
      | none => rfl
      | some p => simp [H.who (List.mem_of_getElem? hj)]
    · rfl

/-- 無効にする（時刻は変えない） -/
def offPair (p : AuraSrc × AuraSrc) : AuraSrc × AuraSrc := ({ p.1 with on := false }, { p.2 with on := false })

/-- 有効に戻す（それぞれ新しい時刻 `N1`・`N2` で） -/
def onPair (N1 N2 : Nat) (p : AuraSrc × AuraSrc) : AuraSrc × AuraSrc :=
  ({ p.1 with on := true, since := N1 }, { p.2 with on := true, since := N2 })

theorem kill (i : Nat) : OrderPairs (P.modify i offPair) := by
  refine ⟨fun q hq => ?_, fun q hq r hr => ?_⟩
  · rcases mem_modify hq with hq | ⟨p, hp, rfl⟩
    · exact H.1 q hq
    · have h := H.1 p hp
      obtain ⟨a, b⟩ := p
      cases a; cases b
      simp only [AuraSrc.mk.injEq] at h
      simp [offPair, h]
  · have hs : ∀ q ∈ P.modify i offPair, ∃ q0 ∈ P, q.1.since = q0.1.since ∧ q.2.since = q0.2.since := by
      intro q hq
      rcases mem_modify hq with hq | ⟨p, hp, rfl⟩
      · exact ⟨q, hq, rfl, rfl⟩
      · exact ⟨p, hp, rfl, rfl⟩
    obtain ⟨q0, hq0, e1, e2⟩ := hs q hq
    obtain ⟨r0, hr0, f1, f2⟩ := hs r hr
    rw [e1, e2, f1, f2]
    exact H.2 q0 hq0 r0 hr0

theorem revive (i : Nat) {N1 N2 : Nat} (h1 : ∀ p ∈ P, p.1.since < N1) (h2 : ∀ p ∈ P, p.2.since < N2) :
    OrderPairs (P.modify i (onPair N1 N2)) := by
  refine ⟨fun q hq => ?_, fun q hq r hr => ?_⟩
  · rcases mem_modify hq with hq | ⟨p, hp, rfl⟩
    · exact H.1 q hq
    · have h := H.1 p hp
      obtain ⟨a, b⟩ := p
      cases a; cases b
      simp only [AuraSrc.mk.injEq] at h
      simp [onPair, h]
  · rcases mem_modify hq with hq | ⟨p, hp, rfl⟩ <;> rcases mem_modify hr with hr | ⟨p', hp', rfl⟩
    · exact H.2 q hq r hr
    · have := h1 q hq; have := h2 q hq
      simp only [onPair]; omega
    · have := h1 r hr; have := h2 r hr
      simp only [onPair]; omega
    · simp [onPair]

/-- **判定を1回進めても、時刻の大小関係が同じまま**（時計の値 `c1`・`c2` は何でもよい）。
どちらも止まるか、どちらも進んで、進んだ後の状態どうしもまた時刻以外が同じで大小関係が同じ。 -/
theorem settleOnce (c1 c2 : Nat) (tp : PlayerId) :
    (YGO.settleOnce (P.map (·.1)) c1 tp = none ∧ YGO.settleOnce (P.map (·.2)) c2 tp = none) ∨
    ∃ P' c1' c2', OrderPairs P' ∧ YGO.settleOnce (P.map (·.1)) c1 tp = some (P'.map (·.1), c1') ∧
      YGO.settleOnce (P.map (·.2)) c2 tp = some (P'.map (·.2), c2') := by
  unfold YGO.settleOnce
  rw [H.findBeaten, H.returnCands]
  cases hf : (P.map (·.1)).findIdx? (fun s => s.on && YGO.beatenIn (P.map (·.1)) s) with
  | some i =>
    right
    refine ⟨P.modify i offPair, c1, c2, H.kill i, ?_, ?_⟩
    · simp only [map_modify P i offPair (·.1) (fun s => { s with on := false }) (fun _ => rfl)]
    · simp only [map_modify P i offPair (·.2) (fun s => { s with on := false }) (fun _ => rfl)]
  | none =>
    cases hr : YGO.returnCands (P.map (·.1)) tp with
    | nil => left; exact ⟨rfl, rfl⟩
    | cons i t =>
      cases t with
      | cons => left; exact ⟨rfl, rfl⟩
      | nil =>
        right
        let N1 := newestTime (P.map (·.1)) c1
        let N2 := newestTime (P.map (·.2)) c2
        have h1 : ∀ p ∈ P, p.1.since < N1 := fun p hp =>
          since_lt_newestTime _ (List.mem_map_of_mem hp)
        have h2 : ∀ p ∈ P, p.2.since < N2 := fun p hp =>
          since_lt_newestTime _ (List.mem_map_of_mem hp)
        refine ⟨P.modify i (onPair N1 N2), N1, N2, H.revive i h1 h2, ?_, ?_⟩
        · simp only [map_modify P i (onPair N1 N2) (·.1) (fun s => { s with on := true, since := N1 })
            (fun _ => rfl), N1]
        · simp only [map_modify P i (onPair N1 N2) (·.2) (fun s => { s with on := true, since := N2 })
            (fun _ => rfl), N2]

/-- 選択待ちで同じ位置 `j` のカードを有効に戻した後も、時刻の大小関係が同じ -/
theorem choose (c1 c2 j : Nat) :
    ∃ P', OrderPairs P' ∧
      (P.map (·.1)).modify j ({ · with on := true, since := newestTime (P.map (·.1)) c1 }) = P'.map (·.1) ∧
      (P.map (·.2)).modify j ({ · with on := true, since := newestTime (P.map (·.2)) c2 }) = P'.map (·.2) := by
  let N1 := newestTime (P.map (·.1)) c1
  let N2 := newestTime (P.map (·.2)) c2
  have h1 : ∀ p ∈ P, p.1.since < N1 := fun p hp => since_lt_newestTime _ (List.mem_map_of_mem hp)
  have h2 : ∀ p ∈ P, p.2.since < N2 := fun p hp => since_lt_newestTime _ (List.mem_map_of_mem hp)
  refine ⟨P.modify j (onPair N1 N2), H.revive j h1 h2, ?_, ?_⟩
  · rw [map_modify P j (onPair N1 N2) (·.1) (fun s => { s with on := true, since := N1 }) (fun _ => rfl)]
  · rw [map_modify P j (onPair N1 N2) (·.2) (fun s => { s with on := true, since := N2 }) (fun _ => rfl)]

theorem onList : (P.map (·.2)).map (·.on) = (P.map (·.1)).map (·.on) := by
  simp only [List.map_map]
  exact List.map_congr_left fun p hp => H.on hp

end OrderPairs


end YGO

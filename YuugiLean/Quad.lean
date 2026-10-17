import YuugiLean.Order

/-!
# 4すくみ（スキルドレイン・王宮のお触れ・サイコ・ショッカー・D－HERO Bloo－D）

D－HERO Bloo－D は判定が必ず止まる条件（`AuraSrc.Simple`）を満たさず、一般には判定が回り続けることがある
（`loopSrcs`）。ここでは、`4すくみ考察.md` の4枚（スキルドレイン・お触れ・ショッカーを同じプレイヤーが、
Bloo－D を相手がコントロールする）について、次を確かめる（`quad_allEnd`）。

* どの状態（4枚それぞれの有効・無効と、適用された順番）から判定しても
* どちらのターンでも
* 選択待ちになったときにどう選んでも

判定は必ず止まり、止まったときは **Bloo－D とお触れが有効、ショッカーとスキルドレインが無効** になる。

適用の時刻は大小関係だけが判定に効く（`Order.lean`）。そこで、まず時刻を 1〜4 の並べ方24通りで表して
すべての場合を調べ（`quad_allEnd` など）、それを互いに異なるどんな時刻・時計の値にも広げる（`quad_allEnd_any` など）。
-/

namespace YGO

/-- 判定の進み方がすべて止まり、止まったときの有効・無効の並びが `E` のどれかになる。
選択待ちでは、選べるどのカードを選んだ場合についても成り立つ。 -/
inductive AllEnd (tp : PlayerId) (E : List (List Bool)) : List AuraSrc → Nat → Prop
  | done {l : List AuraSrc} {c : Nat} : settleOnce l c tp = none → awaitingChoice l tp = none →
      l.map (·.on) ∈ E → AllEnd tp E l c
  | auto {l l' : List AuraSrc} {c c' : Nat} : settleOnce l c tp = some (l', c') → AllEnd tp E l' c' →
      AllEnd tp E l c
  | choose {l : List AuraSrc} {c : Nat} : settleOnce l c tp = none → (awaitingChoice l tp).isSome →
      (∀ j ∈ returnCands l tp,
        AllEnd tp E (l.modify j ({ · with on := true, since := newestTime l c })) (newestTime l c)) →
      AllEnd tp E l c

/-- すべての進み方をたどり、止まったときの有効・無効の並びを集める（`n` はたどる深さの上限） -/
def allEnds (tp : PlayerId) : Nat → List AuraSrc → Nat → Option (List (List Bool))
  | 0, _, _ => none
  | n + 1, l, c =>
    match settleOnce l c tp with
    | some (l', c') => allEnds tp n l' c'
    | none =>
      if (awaitingChoice l tp).isSome then
        ((returnCands l tp).mapM fun j =>
          allEnds tp n (l.modify j ({ · with on := true, since := newestTime l c })) (newestTime l c)).map
          List.flatten
      else some [l.map (·.on)]

theorem mapM_some {α β : Type} {f : α → Option β} {xs : List α} {ys : List β} (h : xs.mapM f = some ys) :
    ∀ x ∈ xs, ∃ y ∈ ys, f x = some y := by
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih =>
    simp only [List.mapM_cons, bind, Option.bind] at h
    cases hx : f x with
    | none => simp [hx] at h
    | some y =>
      cases hr : xs.mapM f with
      | none => simp [hx, hr] at h
      | some ys' =>
        simp only [hx, hr, pure, Option.some.injEq] at h
        subst h
        intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact ⟨y, List.mem_cons_self, hx⟩
        · obtain ⟨w, hw, hfw⟩ := ih hr z hz
          exact ⟨w, List.mem_cons_of_mem _ hw, hfw⟩

/-- `allEnds` で集めた並びがどれも `E` にあれば、すべての進み方が止まり、`E` のどれかになる -/
theorem allEnds_sound {tp : PlayerId} {E : List (List Bool)} :
    ∀ (n : Nat) (l : List AuraSrc) (c : Nat) (R : List (List Bool)),
      allEnds tp n l c = some R → (∀ x ∈ R, x ∈ E) → AllEnd tp E l c := by
  intro n
  induction n with
  | zero => intro l c R h; simp [allEnds] at h
  | succ n ih =>
    intro l c R h hR
    simp only [allEnds] at h
    split at h
    · rename_i l' c' hs
      exact .auto hs (ih l' c' R h hR)
    · rename_i hs
      split at h
      · rename_i ha
        cases hm : (returnCands l tp).mapM fun j =>
            allEnds tp n (l.modify j ({ · with on := true, since := newestTime l c })) (newestTime l c) with
        | none => simp [hm] at h
        | some ys =>
          simp only [hm, Option.map_some, Option.some.injEq] at h
          subst h
          refine .choose hs ha fun j hj => ?_
          obtain ⟨y, hy, hfy⟩ := mapM_some hm j hj
          exact ih _ _ y hfy fun x hx => hR x (List.mem_flatten.mpr ⟨y, hy, hx⟩)
      · rename_i ha
        simp only [Option.some.injEq] at h
        subst h
        have hn : awaitingChoice l tp = none := by simpa using ha
        exact .done hs hn (hR _ List.mem_cons_self)

/-! ## 4枚のカード -/

/-- `quadSrcs` の4枚の、有効・無効と時刻以外。組の数字は、スキルドレイン・お触れ・ショッカー・Bloo－D の順の番号 -/
def quadTemplate (w : PlayerId) (drainFirst : Bool) : List (Nat × AuraSrc) :=
  let mk (i : Nat) (who : PlayerId) (kind : SrcKind) (key : Nat × Nat × Nat) (auras : List Aura) :
      Nat × AuraSrc :=
    (i, { who, kind, key, since := 0, on := false, auras })
  let drain (z : Nat) := mk 0 w .trap (stKey w z) [.negateMonsterEffects]
  let decree (z : Nat) := mk 1 w .trap (stKey w z) [.negateTraps]
  let traps := if drainFirst then [drain 0, decree 1] else [decree 0, drain 1]
  match w with
  | .one => traps ++ [mk 2 .one .monster (monKey 0) [.negateTraps],
                      mk 3 .two .monster (monKey 1) [.negateOppMonsterEffects]]
  | .two => [mk 3 .one .monster (monKey 0) [.negateOppMonsterEffects]] ++ traps ++
              [mk 2 .two .monster (monKey 1) [.negateTraps]]

/-- `w` がスキルドレイン・お触れ・ショッカーを、`w.other` が Bloo－D をコントロールするときの、
盤面の順（P1 の魔法・罠ゾーン、P1 のモンスター、P2 の魔法・罠ゾーン、P2 のモンスター）に並べた4枚。
`drainFirst` はスキルドレインがお触れより左のゾーンにあるか。`on` と `since` はスキルドレイン・お触れ・
ショッカー・Bloo－D の順の、有効かどうかと適用の時刻。 -/
def quadSrcs (w : PlayerId) (drainFirst : Bool) (on : List Bool) (since : List Nat) : List AuraSrc :=
  (quadTemplate w drainFirst).map fun (i, s) => { s with since := since.getD i 0, on := on.getD i false }

/-- 盤面の順に並べたときの、「Bloo－D とお触れが有効、ショッカーとスキルドレインが無効」の並び -/
def quadExpected (w : PlayerId) (drainFirst : Bool) : List Bool :=
  let traps := if drainFirst then [false, true] else [true, false]
  match w with
  | .one => traps ++ [false, true]
  | .two => [true] ++ traps ++ [false]

/-- 4枚の有効・無効の16通り -/
def allOn : List (List Bool) :=
  [false, true].flatMap fun a => [false, true].flatMap fun b => [false, true].flatMap fun c =>
    [false, true].map fun d => [a, b, c, d]

/-- 適用の時刻の順番の24通り -/
def allOrders : List (List Nat) :=
  [[1, 2, 3, 4], [1, 2, 4, 3], [1, 3, 2, 4], [1, 3, 4, 2], [1, 4, 2, 3], [1, 4, 3, 2],
   [2, 1, 3, 4], [2, 1, 4, 3], [2, 3, 1, 4], [2, 3, 4, 1], [2, 4, 1, 3], [2, 4, 3, 1],
   [3, 1, 2, 4], [3, 1, 4, 2], [3, 2, 1, 4], [3, 2, 4, 1], [3, 4, 1, 2], [3, 4, 2, 1],
   [4, 1, 2, 3], [4, 1, 3, 2], [4, 2, 1, 3], [4, 2, 3, 1], [4, 3, 1, 2], [4, 3, 2, 1]]

theorem allOrders_perm : ∀ o ∈ allOrders, o.Perm [1, 2, 3, 4] := by decide

/-! ## 止まった状態は結論の状態だけ -/

/-- 安定な状態：有効なカードはどれも適用中のカードに無効にされず、無効なカードはどれも適用中のカードに
無効にされている。判定が止まり、選択待ちでなければ安定（`settleOnce_none`）。 -/
def Stable (l : List AuraSrc) : Bool :=
  l.all (fun s => !s.on || !beatenIn l s) && l.all (fun s => s.on || beatenIn l s)

theorem stable_of_settled {l : List AuraSrc} {c : Nat} {tp : PlayerId} (h : settleOnce l c tp = none)
    (hw : awaitingChoice l tp = none) : Stable l = true := by
  obtain ⟨h1, h2⟩ := settleOnce_none h
  simp only [Stable, Bool.and_eq_true, List.all_eq_true]
  refine ⟨fun s hs => ?_, fun s hs => ?_⟩
  · cases ho : s.on
    · rfl
    · simp [h1 s hs ho]
  · cases ho : s.on
    · simp [h2 hw s hs ho]
    · rfl

/-- **安定な状態は「Bloo－D とお触れが有効、ショッカーとスキルドレインが無効」だけ**（どの順番で適用されていても）。
`4すくみ考察.md` の不動点による確認に、適用の時刻（互いに無効にし合うときは先に適用された方が優先）を加えたもの。 -/
theorem quad_stable : ∀ w df, ∀ on ∈ allOn, ∀ o ∈ allOrders,
    Stable (quadSrcs w df on o) = true → (quadSrcs w df on o).map (·.on) = quadExpected w df := by
  intro w df
  cases w <;> cases df <;> decide +kernel

/-- **4すくみの判定は、どう進んでも、止まって選択待ちでなければ結論の状態** -/
theorem quad_settled (w : PlayerId) (df : Bool) {on : List Bool} {o : List Nat} (hon : on ∈ allOn)
    (ho : o ∈ allOrders) {tp : PlayerId} {c : Nat} (h : settleOnce (quadSrcs w df on o) c tp = none)
    (hw : awaitingChoice (quadSrcs w df on o) tp = none) :
    (quadSrcs w df on o).map (·.on) = quadExpected w df :=
  quad_stable w df on hon o ho (stable_of_settled h hw)

/-! ## Bloo－D 側のターンなら、どう選んでも止まる -/

/-- 有限個の場合を調べる：どの進み方も32回以内に止まり、止まったときは結論の並び -/
def quadCheck (w : PlayerId) (df : Bool) (tp : PlayerId) : Bool :=
  allOn.all fun on => allOrders.all fun o =>
    match allEnds tp 32 (quadSrcs w df on o) 4 with
    | some R => R.all (· == quadExpected w df)
    | none => false

set_option maxHeartbeats 0 in
theorem quadCheck_ok : ∀ w df, quadCheck w df w.other = true := by
  intro w df
  cases w <;> cases df <;> decide +kernel

/-- **Bloo－D をコントロールするプレイヤーのターンなら、4すくみはどの状態から、どう選んでも、
Bloo－D とお触れが有効、ショッカーとスキルドレインが無効で止まる** -/
theorem quad_allEnd (w : PlayerId) (df : Bool) {on : List Bool} {o : List Nat}
    (hon : on ∈ allOn) (ho : o ∈ allOrders) :
    AllEnd w.other [quadExpected w df] (quadSrcs w df on o) 4 := by
  have h := quadCheck_ok w df
  simp only [quadCheck, List.all_eq_true] at h
  have h := h on hon o ho
  split at h
  · rename_i R hR
    refine allEnds_sound 32 _ _ R hR fun x hx => ?_
    have := List.all_eq_true.mp h x hx
    simpa using this
  · cases h

/-! ## スキルドレイン側のターンでは、選び方によっては回り続ける -/

/-- 選び方のうちどれかで、判定が止まり、止まったときの並びが `E` のどれかになる -/
inductive SomeEnd (tp : PlayerId) (E : List (List Bool)) : List AuraSrc → Nat → Prop
  | done {l : List AuraSrc} {c : Nat} : settleOnce l c tp = none → awaitingChoice l tp = none →
      l.map (·.on) ∈ E → SomeEnd tp E l c
  | auto {l l' : List AuraSrc} {c c' : Nat} : settleOnce l c tp = some (l', c') → SomeEnd tp E l' c' →
      SomeEnd tp E l c
  | choose {l : List AuraSrc} {c : Nat} {j : Nat} : settleOnce l c tp = none → (awaitingChoice l tp).isSome →
      j ∈ returnCands l tp →
      SomeEnd tp E (l.modify j ({ · with on := true, since := newestTime l c })) (newestTime l c) →
      SomeEnd tp E l c

def someEnd (tp : PlayerId) (E : List (List Bool)) : Nat → List AuraSrc → Nat → Bool
  | 0, _, _ => false
  | n + 1, l, c =>
    match settleOnce l c tp with
    | some (l', c') => someEnd tp E n l' c'
    | none =>
      if (awaitingChoice l tp).isSome then
        (returnCands l tp).any fun j =>
          someEnd tp E n (l.modify j ({ · with on := true, since := newestTime l c })) (newestTime l c)
      else E.contains (l.map (·.on))

theorem someEnd_sound {tp : PlayerId} {E : List (List Bool)} :
    ∀ (n : Nat) (l : List AuraSrc) (c : Nat), someEnd tp E n l c = true → SomeEnd tp E l c := by
  intro n
  induction n with
  | zero => intro l c h; simp [someEnd] at h
  | succ n ih =>
    intro l c h
    simp only [someEnd] at h
    split at h
    · rename_i l' c' hs
      exact .auto hs (ih l' c' h)
    · rename_i hs
      split at h
      · rename_i ha
        obtain ⟨j, hj, hr⟩ := List.any_eq_true.mp h
        exact .choose hs ha hj (ih _ _ hr)
      · rename_i ha
        have hn : awaitingChoice l tp = none := by simpa using ha
        exact .done hs hn (by simpa using h)

def quadSomeCheck (w : PlayerId) (df : Bool) : Bool :=
  allOn.all fun on => allOrders.all fun o => someEnd w [quadExpected w df] 32 (quadSrcs w df on o) 4

set_option maxHeartbeats 0 in
theorem quadSomeCheck_ok : ∀ w df, quadSomeCheck w df = true := by
  intro w df
  cases w <;> cases df <;> decide +kernel

/-- **スキルドレイン・お触れ・ショッカーをコントロールするプレイヤーのターンでも、選び方によっては止まる**
（止まれば、`quad_settled` により結論の状態） -/
theorem quad_someEnd (w : PlayerId) (df : Bool) {on : List Bool} {o : List Nat}
    (hon : on ∈ allOn) (ho : o ∈ allOrders) :
    SomeEnd w [quadExpected w df] (quadSrcs w df on o) 4 := by
  have h := quadSomeCheck_ok w df
  simp only [quadSomeCheck, List.all_eq_true] at h
  exact someEnd_sound 32 _ _ (h on hon o ho)

/-- 選択待ちで、j 番目のカードを選び、次に止まるまで進める -/
def quadPick (tp : PlayerId) (j : Nat) (r : List AuraSrc × Nat) : List AuraSrc × Nat :=
  let t := newestTime r.1 r.2
  settle (r.1.modify j ({ · with on := true, since := t })) t tp

/-- 適用の時刻の順番 -/
def timeRanks (l : List AuraSrc) : List Nat := l.map fun s => (l.filter (·.since < s.since)).length

/-- 回り続ける例（P1 のターン。スキルドレイン・お触れ・ショッカー・Bloo－D の順に並ぶ）。
Bloo－D だけが有効で、お触れ・ショッカー・スキルドレイン・Bloo－D の順に適用されていて、
お触れとスキルドレインが同時に有効に戻る選択待ちから：
1. スキルドレインを選ぶ：Bloo－D が無効になり、お触れとショッカーが同時に有効に戻る選択待ちになる
2. ショッカーを選ぶ：ショッカーは新たに適用されたので、先に適用されていたスキルドレインに無効にされる。
   お触れがスキルドレインを無効にし、ショッカーと Bloo－D が同時に有効に戻る。② P1 のターンなのでショッカーが
   先に適用されてお触れを無効にし、Bloo－D がショッカーを無効にする
3. 最初と同じ選択待ち（有効・無効と適用の順番が同じ）に戻る

1. でお触れを選ぶか、2. でお触れを選べば止まる -/
def quadLoopStart : List AuraSrc := quadSrcs .one true [false, false, false, true] [3, 1, 2, 4]

example : awaitingChoice quadLoopStart .one = some .one ∧ returnCands quadLoopStart .one = [0, 1] ∧
    let r1 := quadPick .one 0 (quadLoopStart, 4)
    returnCands r1.1 .one = [1, 2] ∧ r1.1.map (·.on) = [true, false, false, false] ∧
    let r2 := quadPick .one 2 r1
    awaitingChoice r2.1 .one = some .one ∧ r2.1.map (·.on) = quadLoopStart.map (·.on) ∧
      timeRanks r2.1 = timeRanks quadLoopStart := by
  decide

/-! ## 時刻の値を一般にする

判定は時刻の大小関係しか見ない（`OrderPairs`）。互いに異なる時刻4つを、その順位（1〜4 の並べ方、`timeOrder`）に
置き換えても大小関係は変わらないので、上の24通りの結果が、どんな時刻（と時計の値）にもそのまま成り立つ。 -/

/-- 大小関係が同じ2つの状態の一方で、どう選んでも止まり `E` のどれかになるなら、もう一方でも同じ
（時計の値は何でもよい） -/
theorem AllEnd.transfer {tp : PlayerId} {E : List (List Bool)} {l : List AuraSrc} {c : Nat}
    (h : AllEnd tp E l c) : ∀ (P : List (AuraSrc × AuraSrc)), OrderPairs P → P.map (·.1) = l →
      ∀ c2, AllEnd tp E (P.map (·.2)) c2 := by
  induction h with
  | done hs hw hE =>
    intro P H hl c2
    subst hl
    rcases H.settleOnce _ c2 tp with ⟨-, h2⟩ | ⟨P', c1', c2', -, h1, -⟩
    · exact .done h2 (by rw [H.awaitingChoice]; exact hw) (by rw [H.onList]; exact hE)
    · rw [hs] at h1; cases h1
  | auto hs _ ih =>
    intro P H hl c2
    subst hl
    rcases H.settleOnce _ c2 tp with ⟨h1, -⟩ | ⟨P', c1', c2', H', h1, h2⟩
    · rw [hs] at h1; cases h1
    · rw [hs] at h1
      cases h1
      exact .auto h2 (ih P' H' rfl c2')
  | choose hs ha _ ih =>
    intro P H hl c2
    subst hl
    rcases H.settleOnce _ c2 tp with ⟨-, h2⟩ | ⟨P', c1', c2', -, h1, -⟩
    · refine .choose h2 (by rw [H.awaitingChoice]; exact ha) fun j hj => ?_
      rw [H.returnCands] at hj
      obtain ⟨P', H', e1, e2⟩ := H.choose _ c2 j
      rw [e2]
      exact ih j hj P' H' e1.symm _
    · rw [hs] at h1; cases h1

/-- `SomeEnd` も同じ -/
theorem SomeEnd.transfer {tp : PlayerId} {E : List (List Bool)} {l : List AuraSrc} {c : Nat}
    (h : SomeEnd tp E l c) : ∀ (P : List (AuraSrc × AuraSrc)), OrderPairs P → P.map (·.1) = l →
      ∀ c2, SomeEnd tp E (P.map (·.2)) c2 := by
  induction h with
  | done hs hw hE =>
    intro P H hl c2
    subst hl
    rcases H.settleOnce _ c2 tp with ⟨-, h2⟩ | ⟨P', c1', c2', -, h1, -⟩
    · exact .done h2 (by rw [H.awaitingChoice]; exact hw) (by rw [H.onList]; exact hE)
    · rw [hs] at h1; cases h1
  | auto hs _ ih =>
    intro P H hl c2
    subst hl
    rcases H.settleOnce _ c2 tp with ⟨h1, -⟩ | ⟨P', c1', c2', H', h1, h2⟩
    · rw [hs] at h1; cases h1
    · rw [hs] at h1
      cases h1
      exact .auto h2 (ih P' H' rfl c2')
  | @choose l c j hs ha hj _ ih =>
    intro P H hl c2
    subst hl
    rcases H.settleOnce _ c2 tp with ⟨-, h2⟩ | ⟨P', c1', c2', -, h1, -⟩
    · obtain ⟨P', H', e1, e2⟩ := H.choose c c2 j
      refine .choose (j := j) h2 (by rw [H.awaitingChoice]; exact ha) (by rw [H.returnCands]; exact hj) ?_
      rw [e2]
      exact ih P' H' e1.symm _
    · rw [hs] at h1; cases h1

/-- 時刻の順位（1 が最も古い）。互いに異なる時刻なら 1〜n の並べ方になる -/
def timeOrder (s : List Nat) : List Nat := s.map fun x => s.countP (· < x) + 1

theorem countP_lt_iff {s : List Nat} {x y : Nat} (hx : x ∈ s) :
    x < y ↔ s.countP (· < x) < s.countP (· < y) := by
  constructor
  · intro h
    exact countP_lt_of (fun z _ hz => by simp at hz ⊢; omega) ⟨x, hx, by simp [h], by simp⟩
  · intro h
    apply Classical.byContradiction
    intro hn
    have : s.countP (· < y) ≤ s.countP (· < x) :=
      List.countP_mono_left fun z _ hz => by simp at hz ⊢; omega
    omega

theorem timeOrder_getD {s : List Nat} {i : Nat} (hi : i < s.length) :
    (timeOrder s).getD i 0 = s.countP (· < s.getD i 0) + 1 ∧ s.getD i 0 ∈ s := by
  refine ⟨?_, ?_⟩
  · simp [timeOrder, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]

theorem timeOrder_lt {s : List Nat} {i j : Nat} (hi : i < s.length) (hj : j < s.length) :
    (timeOrder s).getD i 0 < (timeOrder s).getD j 0 ↔ s.getD i 0 < s.getD j 0 := by
  obtain ⟨e1, m1⟩ := timeOrder_getD hi
  obtain ⟨e2, -⟩ := timeOrder_getD hj
  rw [e1, e2, countP_lt_iff m1]
  omega

theorem perm4 : ∀ a ∈ [1, 2, 3, 4], ∀ b ∈ [1, 2, 3, 4], ∀ c ∈ [1, 2, 3, 4], ∀ d ∈ [1, 2, 3, 4],
    [a, b, c, d].Nodup → [a, b, c, d] ∈ allOrders := by decide

/-- 互いに異なる時刻4つの順位は、24通りのどれか -/
theorem timeOrder_mem {s : List Nat} (hl : s.length = 4) (hs : s.Nodup) : timeOrder s ∈ allOrders := by
  have hb : ∀ x ∈ timeOrder s, x ∈ [1, 2, 3, 4] := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    have : s.countP (· < y) < s.countP (fun _ => true) :=
      countP_lt_of (fun _ _ _ => by simp) ⟨y, hy, by simp, by simp⟩
    rw [List.countP_true, hl] at this
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega
  have hn : (timeOrder s).Nodup := by
    unfold timeOrder List.Nodup
    rw [List.pairwise_map]
    refine List.Pairwise.imp_of_mem (fun {x y} hx hy hxy hn => ?_) hs
    have h1 := countP_lt_iff (y := y) hx
    have h2 := countP_lt_iff (y := x) hy
    simp only [Nat.add_right_cancel_iff] at hn
    omega
  have hl' : (timeOrder s).length = 4 := by simp [timeOrder, hl]
  match h : timeOrder s, hl' with
  | [a, b, c, d], _ =>
    rw [h] at hb hn
    exact perm4 a (hb a (by simp)) b (hb b (by simp)) c (hb c (by simp)) d (hb d (by simp)) hn

theorem allOn_mem {on : List Bool} (hl : on.length = 4) : on ∈ allOn := by
  match on, hl with
  | [a, b, c, d], _ => cases a <;> cases b <;> cases c <;> cases d <;> decide

theorem quadTemplate_lt : ∀ w df, ∀ p ∈ quadTemplate w df, p.1 < 4 := by
  intro w df; cases w <;> cases df <;> decide

/-- 同じ有効・無効で、時刻が `o`（順位）と `s` の4枚を組にしたもの -/
def quadPairs (w : PlayerId) (df : Bool) (on : List Bool) (o s : List Nat) : List (AuraSrc × AuraSrc) :=
  (quadTemplate w df).map fun (i, x) =>
    ({ x with since := o.getD i 0, on := on.getD i false }, { x with since := s.getD i 0, on := on.getD i false })

theorem quadPairs_ok (w : PlayerId) (df : Bool) (on : List Bool) {s : List Nat} (hl : s.length = 4) :
    OrderPairs (quadPairs w df on (timeOrder s) s) ∧
      (quadPairs w df on (timeOrder s) s).map (·.1) = quadSrcs w df on (timeOrder s) ∧
      (quadPairs w df on (timeOrder s) s).map (·.2) = quadSrcs w df on s := by
  refine ⟨⟨fun p hp => ?_, fun p hp q hq => ?_⟩, by simp [quadPairs, quadSrcs], by simp [quadPairs, quadSrcs]⟩
  · obtain ⟨⟨i, x⟩, -, rfl⟩ := List.mem_map.mp hp
    rfl
  · obtain ⟨⟨i, x⟩, hi, rfl⟩ := List.mem_map.mp hp
    obtain ⟨⟨j, y⟩, hj, rfl⟩ := List.mem_map.mp hq
    have hi := quadTemplate_lt w df _ hi
    have hj := quadTemplate_lt w df _ hj
    exact timeOrder_lt (s := s) (by rw [hl]; exact hi) (by rw [hl]; exact hj)

/-- **4すくみ：互いに異なるどんな時刻で適用されていても、Bloo－D をコントロールするプレイヤーのターンなら、
どの状態から、どう選んでも、Bloo－D とお触れが有効、ショッカーとスキルドレインが無効で止まる**
（時計の値 `c` も何でもよい） -/
theorem quad_allEnd_any (w : PlayerId) (df : Bool) {on : List Bool} {s : List Nat}
    (hon : on.length = 4) (hl : s.length = 4) (hs : s.Nodup) (c : Nat) :
    AllEnd w.other [quadExpected w df] (quadSrcs w df on s) c := by
  obtain ⟨H, e1, e2⟩ := quadPairs_ok w df on hl
  rw [← e2]
  exact (quad_allEnd w df (allOn_mem hon) (timeOrder_mem hl hs)).transfer _ H e1 c

/-- **互いに異なるどんな時刻でも、スキルドレイン側のターンで、選び方によっては止まる** -/
theorem quad_someEnd_any (w : PlayerId) (df : Bool) {on : List Bool} {s : List Nat}
    (hon : on.length = 4) (hl : s.length = 4) (hs : s.Nodup) (c : Nat) :
    SomeEnd w [quadExpected w df] (quadSrcs w df on s) c := by
  obtain ⟨H, e1, e2⟩ := quadPairs_ok w df on hl
  rw [← e2]
  exact (quad_someEnd w df (allOn_mem hon) (timeOrder_mem hl hs)).transfer _ H e1 c

/-- **互いに異なるどんな時刻でも、止まって選択待ちでなければ結論の状態** -/
theorem quad_settled_any (w : PlayerId) (df : Bool) {on : List Bool} {s : List Nat}
    (hon : on.length = 4) (hl : s.length = 4) (hs : s.Nodup) {tp : PlayerId} {c : Nat}
    (h : settleOnce (quadSrcs w df on s) c tp = none) (hw : awaitingChoice (quadSrcs w df on s) tp = none) :
    (quadSrcs w df on s).map (·.on) = quadExpected w df := by
  obtain ⟨H, e1, e2⟩ := quadPairs_ok w df on hl
  rw [← e2] at h hw ⊢
  rw [H.awaitingChoice, e1] at hw
  rw [H.onList, e1]
  rcases H.settleOnce c c tp with ⟨h1, -⟩ | ⟨P', c1', c2', -, -, h2⟩
  · rw [e1] at h1
    exact quad_settled w df (allOn_mem hon) (timeOrder_mem hl hs) h1 hw
  · rw [h] at h2; cases h2

end YGO

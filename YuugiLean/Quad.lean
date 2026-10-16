import YuugiLean.Settle

/-!
# 4すくみ（スキルドレイン・王宮のお触れ・サイコ・ショッカー・D－HERO Bloo－D）

D－HERO Bloo－D は判定が必ず止まる条件（`AuraSrc.Simple`）を満たさず、一般には判定が回り続けることがある
（`loopSrcs`）。ここでは、`4すくみ考察.md` の4枚（スキルドレイン・お触れ・ショッカーを同じプレイヤーが、
Bloo－D を相手がコントロールする）について、次を確かめる（`quad_allEnd`）。

* どの状態（4枚それぞれの有効・無効と、適用された順番）から判定しても
* どちらのターンでも
* 選択待ちになったときにどう選んでも

判定は必ず止まり、止まったときは **Bloo－D とお触れが有効、ショッカーとスキルドレインが無効** になる。

適用の時刻は順番だけが判定に効くので、1〜4 の並べ方24通りで表す（時刻の値そのものを一般にした証明はしていない）。
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

/-- `w` がスキルドレイン・お触れ・ショッカーを、`w.other` が Bloo－D をコントロールするときの、
盤面の順（P1 の魔法・罠ゾーン、P1 のモンスター、P2 の魔法・罠ゾーン、P2 のモンスター）に並べた4枚。
`drainFirst` はスキルドレインがお触れより左のゾーンにあるか。`on` と `since` はスキルドレイン・お触れ・
ショッカー・Bloo－D の順の、有効かどうかと適用の時刻。 -/
def quadSrcs (w : PlayerId) (drainFirst : Bool) (on : List Bool) (since : List Nat) : List AuraSrc :=
  let mk (i : Nat) (who : PlayerId) (kind : SrcKind) (key : Nat × Nat × Nat) (auras : List Aura) : AuraSrc :=
    { who, kind, key, since := since.getD i 0, on := on.getD i false, auras }
  let drain (z : Nat) := mk 0 w .trap (stKey w z) [.negateMonsterEffects]
  let decree (z : Nat) := mk 1 w .trap (stKey w z) [.negateTraps]
  let traps := if drainFirst then [drain 0, decree 1] else [decree 0, drain 1]
  match w with
  | .one => traps ++ [mk 2 .one .monster (monKey 0) [.negateTraps],
                      mk 3 .two .monster (monKey 1) [.negateOppMonsterEffects]]
  | .two => [mk 3 .one .monster (monKey 0) [.negateOppMonsterEffects]] ++ traps ++
              [mk 2 .two .monster (monKey 1) [.negateTraps]]

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

end YGO

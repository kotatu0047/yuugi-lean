import Lean
import Spec.Statements

/-!
# 検査：CardGen の定理が凍結した主張を証明していること

各行の `theorem` は、`CardGen` の定理の型が `Spec.Statements` の主張と一致するときだけ通る
（命題のすり替え・余計な仮定を弾く）。`#assert_std_axioms` は、使う公理が `propext`・`Classical.choice`・
`Quot.sound` だけであることを確かめる（`sorry`＝`sorryAx`、独自の `axiom`、`native_decide`＝`Lean.ofReduceBool` を弾く）。

`Checked` の一覧と、レポートが名前を出す定理の一致は `spec/check.sh` が確かめる。
-/

open Lean Elab Command in
/-- 定数 `id` が使う公理が、標準の3つだけであることを確かめる -/
elab "#assert_std_axioms " id:ident : command => do
  let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let axs ← liftCoreM <| collectAxioms n
  let ok := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := axs.filter (fun a => !ok.contains a)
  unless bad.isEmpty do
    throwError "許可していない公理を使っています（{n}）：{bad}"

namespace Spec.Checked

theorem derived_valid : Spec.derived_valid := @CardGen.derived_valid
theorem gameClaims_valid : Spec.gameClaims_valid := @CardGen.gameClaims_valid
theorem negation_settles : Spec.negation_settles := @CardGen.negation_settles
theorem allEnd_of_certOK : Spec.allEnd_of_certOK := @CardGen.TSys.allEnd_of_certOK
theorem step?_sound : Spec.step?_sound := @CardGen.step?_sound
theorem cards_perm : Spec.cards_perm := @CardGen.Reachable.cards_perm
theorem deck_suffix : Spec.deck_suffix := @CardGen.Reachable.deck_suffix
theorem grave_prefix : Spec.grave_prefix := @CardGen.Step.grave_prefix
theorem step?_grave_prefix : Spec.step?_grave_prefix := @CardGen.Match.step?_grave_prefix
theorem of_reachable : Spec.of_reachable := @CardGen.TReachable.of_reachable
theorem summons_le : Spec.summons_le := @CardGen.TReachable.summons_le
theorem placed_le : Spec.placed_le := @CardGen.TReachable.placed_le
theorem fits : Spec.fits := @CardGen.TReachable.fits
theorem attacked_bagLe : Spec.attacked_bagLe := @CardGen.TReachable.attacked_bagLe
theorem spent_le : Spec.spent_le := @CardGen.TReachable.spent_le
theorem stack_fits : Spec.stack_fits := @CardGen.TReachable.stack_fits
theorem mana_from : Spec.mana_from := @CardGen.TReachable.mana_from
theorem pending_triggered : Spec.pending_triggered := @CardGen.TReachable.pending_triggered
theorem step?_over : Spec.step?_over := @CardGen.Match.step?_over
theorem endTurn_clean : Spec.endTurn_clean := @CardGen.Match.endTurn_clean
theorem endTurn_hand : Spec.endTurn_hand := @CardGen.Match.endTurn_hand
theorem step?_pending : Spec.step?_pending := @CardGen.Match.step?_pending
theorem step?_prio : Spec.step?_prio := @CardGen.Match.step?_prio

end Spec.Checked

#assert_std_axioms Spec.Checked.derived_valid
#assert_std_axioms Spec.Checked.gameClaims_valid
#assert_std_axioms Spec.Checked.negation_settles
#assert_std_axioms Spec.Checked.allEnd_of_certOK
#assert_std_axioms Spec.Checked.step?_sound
#assert_std_axioms Spec.Checked.cards_perm
#assert_std_axioms Spec.Checked.deck_suffix
#assert_std_axioms Spec.Checked.grave_prefix
#assert_std_axioms Spec.Checked.step?_grave_prefix
#assert_std_axioms Spec.Checked.of_reachable
#assert_std_axioms Spec.Checked.summons_le
#assert_std_axioms Spec.Checked.placed_le
#assert_std_axioms Spec.Checked.fits
#assert_std_axioms Spec.Checked.attacked_bagLe
#assert_std_axioms Spec.Checked.spent_le
#assert_std_axioms Spec.Checked.stack_fits
#assert_std_axioms Spec.Checked.mana_from
#assert_std_axioms Spec.Checked.pending_triggered
#assert_std_axioms Spec.Checked.step?_over
#assert_std_axioms Spec.Checked.endTurn_clean
#assert_std_axioms Spec.Checked.endTurn_hand
#assert_std_axioms Spec.Checked.step?_pending
#assert_std_axioms Spec.Checked.step?_prio

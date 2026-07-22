/-
Copyright (c) 2026 Noam Zilberstein. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noam Zilberstein
-/
import Mathlib.Data.Nat.Basic
import Mathlib.Order.OmegaCompletePartialOrder

namespace OmegaCompletePartialOrder
namespace Chain

section Shift

def shift {X : Type} [Preorder X] (c : Chain X) : Chain X := {
  toFun n := c (n + 1)
  monotone' _ _ hle := c.monotone' <| Nat.add_le_add hle (le_refl _)
}

lemma ωSup_shift {X : Type} [OmegaCompletePartialOrder X] (c : Chain X) :
    ωSup c = ωSup c.shift := by
  refine le_antisymm ?_ ?_
  · refine ωSup_le _ _ ?_; intro i
    refine le_trans ?_ (le_ωSup _ i)
    exact c.monotone' <| Nat.le_succ _
  · refine ωSup_le _ _ ?_; intro i
    exact le_ωSup _ (i + 1)

end Shift

section Const

def const {X : Type} [Preorder X] (x : X) : Chain X := {
  toFun _ := x
  monotone' _ _ _ := le_refl _
}

lemma ωSup_const {X : Type} [OmegaCompletePartialOrder X] (x : X) :
    ωSup (const x) = x := by
  refine le_antisymm ?_ ?_
  · refine ωSup_le _ _ ?_; intro n; exact le_refl _
  · exact le_ωSup (const x) 0

end Const

end Chain

lemma ωSup_apply {X Y : Type} [OmegaCompletePartialOrder Y] (c : Chain (X → Y)) (x : X) :
    ωSup c x = ωSup {
      toFun n := c n x
      monotone' _ _ hle := c.monotone' hle x
    } := rfl

end OmegaCompletePartialOrder

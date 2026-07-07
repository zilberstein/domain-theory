/-
Copyright (c) 2026 Noam Zilberstein. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noam Zilberstein
-/
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.OmegaCompletePartialOrder
import DomainTheory.DSet
/-!
  In Mathlib, `CompletePartialOrder` is pointed. Here is a version that does not
   require the domain to be pointed, but requires directed sets to be nonempty.
   It is based on Definition 2.1.13 of Abramsky and Jung 1995
-/

class DCPO (α : Type*) extends PartialOrder α where
  dSup : DSet α → α
  lubOfDirected (d : DSet α) : IsLUB d.val (dSup d)

instance {α : Type*} [CompletePartialOrder α] : DCPO α where
  dSup d := sSup d.val
  lubOfDirected d := CompletePartialOrder.lubOfDirected d.val d.property.1

namespace DSet

def dSup {α : Type*} [DCPO α] : DSet α → α := DCPO.dSup

def le_dSup {α : Type*} [DCPO α] {d : DSet α} {x : α} :
    x ∈ d → x ≤ d.dSup := by
  intro hx; exact (DCPO.lubOfDirected d).1 hx

def dSup_le {α : Type*} [DCPO α] {d : DSet α} {x : α} :
    (∀ y ∈ d, y ≤ x) → d.dSup ≤ x := by
  intro hx; exact (DCPO.lubOfDirected d).2 hx

def ScottContinuous {α β : Type*} [DCPO α] [DCPO β] {f : α → β} (hf : Monotone f) : Prop :=
  ∀ d : DSet α, f d.dSup = (d.image f hf).dSup

end DSet

open OmegaCompletePartialOrder

namespace Chain

def to_dSet {α : Type*} [DCPO α] (c : Chain α) : DSet α :=
  ⟨ Set.range c, by {
    constructor
    · intro x hx y hy
      obtain ⟨n, rfl⟩ := Set.mem_range.mp hx
      obtain ⟨m, rfl⟩ := Set.mem_range.mp hy
      refine ⟨c (max n m), Set.mem_range.mpr ⟨max n m, rfl⟩, ?_, ?_⟩
      · exact c.monotone' le_sup_left
      · exact c.monotone' le_sup_right
    · exact ⟨(c 0), Set.mem_range.mpr ⟨0, rfl⟩⟩
  } ⟩

def lfp {α : Type*} [OmegaCompletePartialOrder α] [OrderBot α]
    (f : α → α) (hf : Monotone f) : α :=
  ωSup (fixedPoints.iterateChain ⟨f, hf⟩ ⊥ bot_le)

theorem lfp_is_lfp {α : Type*} [OmegaCompletePartialOrder α] [OrderBot α]
    {f : α → α} (hc : ωScottContinuous f) :
    IsLeast f.fixedPoints (lfp f hc.monotone) := by
  let f' := ContinuousHom.mk ⟨f, _⟩ hc.map_ωSup
  constructor
  · exact fixedPoints.ωSup_iterate_mem_fixedPoint f' _ _
  · intro x hx; exact fixedPoints.ωSup_iterate_le_fixedPoint f' _ _ hx bot_le

end Chain

-- Derived Instances

instance {α : Type*} [DCPO α] : OmegaCompletePartialOrder α where
  ωSup c := (Chain.to_dSet c).dSup
  le_ωSup c i := DSet.le_dSup (Set.mem_range.mpr ⟨i, rfl⟩)
  ωSup_le c x h := by
    refine DSet.dSup_le ?_; intro d hd
    obtain ⟨i, rfl⟩ := Set.mem_range.mp hd
    exact h i

namespace Function

lemma apply_monotone {α β : Type*} [Preorder β] (x : α) : Monotone (fun f : α → β ↦ f x) :=
  fun _ _ hle ↦ hle x

end Function

instance {α β : Type*} [DCPO β] : DCPO (α → β) where
  dSup d := fun x ↦ DSet.dSup (d.image _ (Function.apply_monotone x))
  lubOfDirected := by
    intro d; constructor
    · intro f hf x; exact DSet.le_dSup (DSet.mem_image hf)
    · intro f hf x; refine DSet.dSup_le ?_
      intro y hy; obtain ⟨g, hg, rfl⟩ := DSet.mem_image_iff.mp hy
      exact hf hg x

instance {X Y : Type} [LE Y] [OrderBot Y] : OrderBot (X → Y) where
  bot_le _ _ := bot_le

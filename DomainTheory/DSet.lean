/-
Copyright (c) 2026 Noam Zilberstein. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noam Zilberstein
-/
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.CompletePartialOrder

/-!
# Directed Sets

A libarary for directed sets based on Definition 2.1.8 of Abramsky and Jung 1995.
-/

def DSet (α : Type*) [LE α] := { s : Set α // DirectedOn LE.le s ∧ s.Nonempty }

namespace DSet

def directed {α : Type*} [LE α] (d : DSet α) : DirectedOn LE.le d.val := d.property.1
def nonempty {α : Type*} [LE α] (d : DSet α) : d.val.Nonempty := d.property.2

instance {α : Type*} [LE α] : HasSubset (DSet α) where
  Subset d d' := d.val ⊆ d'.val

instance {α : Type*} [LE α] : LE (DSet α) where
  le d d' := d ⊆ d'
instance {α : Type*} [LE α] : PartialOrder (DSet α) where
  le_refl d := le_refl d.val
  le_trans d₁ d₂ d₃ := @le_trans _ _ d₁.val d₂.val d₃.val
  le_antisymm _ _ hle hge := Subtype.val_injective (le_antisymm hle hge)

instance {α : Type*} [LE α] : SetLike (DSet α) α where
  coe d := d.val
  coe_injective := Subtype.val_injective

def singleton {α : Type*} [Preorder α] (x : α) : DSet α := {
  val := {x}
  property := by
    constructor
    · simp only [DirectedOn, Set.mem_singleton_iff, exists_eq_left, forall_eq, and_self]
      exact le_refl _
    · exact ⟨x, Set.mem_singleton _⟩
}

def image {α β : Type*} [Preorder α] [Preorder β] (d : DSet α) (f : α → β)
    (hf : Monotone f) : DSet β := {
  val := f '' d.val
  property := by
    obtain ⟨hd, hne⟩ := d.property
    refine ⟨?_, hne.image _⟩
    intro _ hy₁ _ hy₂
    simp only [Set.mem_image, exists_exists_and_eq_and] at *
    obtain ⟨x₁, hx₁, rfl⟩ := hy₁
    obtain ⟨x₂, hx₂, rfl⟩ := hy₂
    obtain ⟨x, hx, hle₁, hle₂⟩ := hd _ hx₁ _ hx₂
    exact ⟨x, hx, hf hle₁, hf hle₂⟩
}

lemma mem_image {α β : Type*} [Preorder α] [Preorder β] {d : DSet α} {x : α}
    {f : α → β} {hf : Monotone f} (h : x ∈ d) : f x ∈ d.image f hf := by
  exact Set.mem_image_of_mem _ h

lemma mem_image_iff {α β : Type*} [Preorder α] [Preorder β] {d : DSet α} {y : β}
    {f : α → β} {hf : Monotone f} :
    y ∈ d.image f hf ↔ ∃ x ∈ d, f x = y := by
  constructor
  · intro h; exact (Set.mem_image f _ y).mp h
  · rintro ⟨x, hx, rfl⟩; exact mem_image hx

lemma image_mono {α β : Type*} [Preorder α] [Preorder β] {f : α → β}
    {hf : Monotone f} : Monotone (fun d : DSet α ↦ d.image f hf) := by
  intro d d' hle y hy
  obtain ⟨x, hx, rfl⟩ := (Set.mem_image _ _ _).mp hy
  exact mem_image (hle hx)

-- A directed set contains upper bounds of all of its finite subsets
lemma finite_upper_bound {α : Type*} [Preorder α] {d : DSet α} {s : Set α}
    (hsub : s ⊆ d) (hfin : s.Finite) :
    ∃ x ∈ d, x ∈ upperBounds s := by
  refine hfin.induction_on_subset s ?_ ?_
  · obtain ⟨x, hx⟩ := d.nonempty
    refine ⟨x, hx, ?_⟩; intro β hc; exfalso; exact hc
  · intro x t hx hst hnt ⟨y, hy, hub⟩
    obtain ⟨z, hz, hxz, hyz⟩ := d.directed _ (hsub hx) _ hy
    refine ⟨z, hz, ?_⟩; intro z' hz'
    rcases Set.mem_insert_iff.mp hz' with rfl | ht
    · exact hxz
    · exact (hub ht).trans hyz

def insert {X : Type} [Preorder X] {x : X} {d d' : DSet X}
    (hfin : d.val.Finite) (hsub : d ⊆ d') (hmem : x ∈ d') : DSet X :=
  have hu := finite_upper_bound (Set.insert_subset hmem hsub) (hfin.insert x)
  {
    val := (d.val.insert x).insert hu.choose
    property := by
      constructor
      · intro y hy z hz
        refine ⟨hu.choose, Set.mem_insert _ _, ?_, ?_⟩ <;>
        rcases Set.eq_or_mem_of_mem_insert hy with rfl | hy <;>
          rcases Set.eq_or_mem_of_mem_insert hz with rfl | hz
        all_goals {
          try (exact le_refl _)
          try (refine hu.choose_spec.2 ?_; assumption)
        }
      · exact ⟨hu.choose, Set.mem_insert _ _⟩
  }

end DSet

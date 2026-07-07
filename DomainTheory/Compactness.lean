/-
Copyright (c) 2026 Noam Zilberstein. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noam Zilberstein
-/
import DomainTheory.DCPO
/-!
Based on Section 2.2.1 of Abramsky and Jung 1995
-/

def way_below {α : Type*} [DCPO α] (x y : α) : Prop :=
    ∀ d : DSet α,
      y ≤ d.dSup →
      ∃ z ∈ d, x ≤ z
infix:30 "≪" => way_below

def IsScottCompact {α : Type*} [DCPO α] (x : α) : Prop := x ≪ x

lemma bot_compact {α : Type*} [DCPO α] [OrderBot α] :
    IsScottCompact (⊥ : α) := by
  intro ⟨_, _, ⟨z, hz⟩⟩ _; exact ⟨z, hz, bot_le⟩

class ScottCompact (α : Type) [DCPO α] where
  scottCompact (x : α) : IsScottCompact x

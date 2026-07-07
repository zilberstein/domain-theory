/-
Copyright (c) 2026 Noam Zilberstein. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noam Zilberstein
-/
import DomainTheory.DCPO
/-!
Based on Section 2.2.1 of Abramsky and Jung 1995
-/

def WayBelow {α : Type*} [DCPO α] (x y : α) : Prop :=
  ∀ d : DSet α,
    y ≤ d.dSup →
    ∃ z ∈ d, x ≤ z
infix:30 " ≪ " => WayBelow

namespace WayBelow

lemma to_le {α : Type*} [DCPO α] {x y : α} (h : x ≪ y) : x ≤ y := by
  have ⟨z, hz, hle⟩ :=
    h (DSet.singleton y) (DSet.le_dSup (Set.mem_singleton _))
  rcases Set.mem_singleton_iff.mp hz with rfl
  exact hle

end WayBelow

def IsScottCompact {α : Type*} [DCPO α] (x : α) : Prop := x ≪ x

lemma bot_compact {α : Type*} [DCPO α] [OrderBot α] :
    IsScottCompact (⊥ : α) := by
  intro ⟨_, _, ⟨z, hz⟩⟩ _; exact ⟨z, hz, bot_le⟩

class ScottCompact (α : Type) [DCPO α] where
  scottCompact (x : α) : IsScottCompact x

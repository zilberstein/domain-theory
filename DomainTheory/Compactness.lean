import DomainTheory.DCPO

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

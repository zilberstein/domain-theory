/-
Copyright (c) 2026 Noam Zilberstein. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noam Zilberstein, Aristotle (Harmonic)
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Preimage
import Mathlib.Data.Finset.Union
import Mathlib.Order.BourbakiWitt
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.SetTheory.Ordinal.Basic

import DomainTheory.DCPO

/-!
# Markowsky's Theorem

This file proves that a poset is a `DCPO` iff it is a `ChainCompletePartialOrder`. The proof is
originally due to Markowsky [[1976]](https://doi.org/10.1007/BF02485815). The proof here follows the
structure of Theorem C.2 from [supplementary lecture](https://www.cs.cornell.edu/courses/cs6110/2023sp/lectures/lecC.pdf)
notes from Cornell's CS 6110 course, and was formalized by Harmonic's Aristotle tool.

The forward implication (directed-complete ⇒ chain-complete) is immediate because chains are
directed. The converse is Markowsky's theorem, proved by transfinite induction on cardinality
(via an Iwamura-style decomposition of a directed set into a chain of directed subsets of strictly
smaller cardinality).
-/

namespace NonemptyChain

def cSup {α : Type*} [ChainCompletePartialOrder α] : NonemptyChain α → α :=
  ChainCompletePartialOrder.cSup

def to_dSet {α : Type*} [Preorder α] (c : NonemptyChain α) : DSet α := {
  val := c.carrier
  property := by
    constructor
    · intro x hx y hy; by_cases heq : x = y
      · subst heq; exact ⟨x, hx, le_refl _, le_refl _⟩
      · rcases c.isChain' hx hy heq with hle | hle
        · exact ⟨y, hy, hle, le_refl _⟩
        · exact ⟨x, hx, le_refl _, hle⟩
    · exact c.Nonempty'
}

end NonemptyChain

open Set

namespace ChainCompletePartialOrder

-- Trivial direction: construct a chain complete partial order from a dcpo
@[reducible]
def of_DCPO {α : Type*} (d : DCPO α) : ChainCompletePartialOrder α where
  cSup c := c.to_dSet.dSup
  le_cSup _ _ hx := DSet.le_dSup hx
  cSup_le _ _ hle := DSet.dSup_le hle

end ChainCompletePartialOrder

section Markowsky

variable {α : Type*} [ChainCompletePartialOrder α]

open ChainCompletePartialOrder

/-
**Gluing lemma.** If `c` is a chain whose members lie below every upper bound of `A`, and
every element of `A` is dominated by some member of `c`, then `A` has a least upper bound (namely
the supremum of `c`, which exists by chain-completeness).
-/
lemma isLUB_of_chain_dominating (A : Set α) (c : NonemptyChain α)
    (hcover : ∀ x ∈ A, ∃ y ∈ c, x ≤ y)
    (hbelow : ∀ x ∈ c, x ∈ lowerBounds (upperBounds A)) :
    IsLUB A c.cSup := by
  refine ⟨ ?_, fun y hy => ?_ ⟩
  · intro x hx; have ⟨y, hy, hle⟩ := hcover x hx
    exact hle.trans (le_cSup _ _ hy)
  · refine cSup_le _ _ ?_; intro x hx; exact hbelow x hx hy

/-- A monotone choice of upper bounds on finite subsets of `A`, defined by strong recursion on
`⊆`: `monoUB F` is a chosen upper bound (inside `A`) of `F` together with all previously chosen
values `monoUB G` for proper subsets `G ⊂ F` (restricted to those lying in `A`). -/
noncomputable def monoUB (A : DSet α) : Finset α → α := by
  classical
  exact Finset.strongInduction fun (F : Finset α) ih =>
    let prev : Finset α :=
      (F.powerset.erase F).image (fun G => if h : G ⊂ F then ih G h else A.nonempty.some)
    let T : Finset α := (F ∪ prev).filter (· ∈ A)
    (A.finset_upper_bound T (by
      intro x hx; simp only [Finset.mem_filter, Finset.mem_union, T] at hx;
      exact hx.2)).choose

open Classical in
/-- The defining recursion equation for `monoUB`. -/
lemma monoUB_eq (A : DSet α) (F : Finset α) :
    monoUB A F =
      (A.finset_upper_bound
        (((F ∪ (F.powerset.erase F).image
            (fun G => if _h : G ⊂ F then monoUB A G else A.nonempty.some)).filter (· ∈ A)))
        (by intro x hx; simp only [Finset.mem_filter] at hx; exact hx.2)).choose := by
  rw [monoUB, Finset.strongInduction_eq]

open Classical in
/-- The specification satisfied by `monoUB F`: it lies in `A` and dominates every relevant element.
-/
lemma monoUB_spec (A : DSet α) (F : Finset α) :
    monoUB A F ∈ A ∧
    ∀ x ∈ (((F ∪ (F.powerset.erase F).image
            (fun G => if _h : G ⊂ F then monoUB A G else A.nonempty.some)).filter (· ∈ A))),
      x ≤ monoUB A F := by
  rw [monoUB_eq]
  exact (A.finset_upper_bound _ (by
    intro x hx; simp only [Finset.mem_filter] at hx; exact hx.2)).choose_spec

open Classical in
/-- A *monotone* choice of upper bounds: a function `b` on finite sets such that, for finite
`F ⊆ A`, `b F ∈ A` is an upper bound of `F`, and `b` is monotone under `⊆` (on finite subsets of
`A`). Constructed by strong recursion on `⊆`. -/
lemma exists_mono_ub (A : DSet α) :
    ∃ b : Finset α → α,
      (∀ F : Finset α, ↑F ⊆ A.carrier → b F ∈ A) ∧
      (∀ F : Finset α, ↑F ⊆ A.carrier → ∀ x ∈ F, x ≤ b F) ∧
      (∀ F G : Finset α, ↑F ⊆ A.carrier → ↑G ⊆ A.carrier → F ⊆ G → b F ≤ b G) := by
  refine ⟨monoUB A, ?_, ?_, ?_⟩
  · intro F _; exact (monoUB_spec A F).1
  · intro F hF x hxF
    apply (monoUB_spec A F).2
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_union_left _ hxF, hF (Finset.mem_coe.mpr hxF)⟩
  · intro F G hF hG hFG
    rcases eq_or_ne F G with rfl | hne'
    · exact le_refl _
    · have hFG' : F ⊂ G := Finset.ssubset_iff_subset_ne.mpr ⟨hFG, hne'⟩
      apply (monoUB_spec A G).2
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_union_right _ ?_, (monoUB_spec A F).1⟩
      rw [Finset.mem_image]
      exact ⟨F, by rw [Finset.mem_erase, Finset.mem_powerset]; exact ⟨hne', hFG⟩,
        by rw [dif_pos hFG']⟩

/-
An infinite set `A` is covered by a `⊆`-chain of subsets, each of strictly smaller
cardinality (the initial-segment filtration coming from a well-ordering of `A`).
-/
omit [ChainCompletePartialOrder α] in
lemma exists_filtration (A : Set α) (hinf : A.Infinite) :
    ∃ 𝔈 : NonemptyChain (Set α),
      (∀ E ∈ 𝔈, E ⊆ A ∧ Cardinal.mk E < Cardinal.mk A) ∧
      (∀ a ∈ A, ∃ E ∈ 𝔈, a ∈ E) := by
  have ⟨e⟩ : Nonempty ((Cardinal.ord (Cardinal.mk A)).ToType ≃ {x : α // x ∈ A}) :=
    Cardinal.eq.mp ( by { simp only [Cardinal.mk_toType, Cardinal.card_ord] } )
  classical
  haveI hAinf : Infinite A := hinf.to_subtype
  have haleph : Cardinal.aleph0 ≤ Cardinal.mk A := Cardinal.infinite_iff.mp hAinf
  set E : (Cardinal.mk A).ord.ToType → Set α :=
    fun j => Subtype.val ∘ e '' {i | i < j} with hE
  have hEmono : ∀ j k : (Cardinal.mk A).ord.ToType, j ≤ k → E j ⊆ E k := by
    intro j k hjk; exact Set.image_mono (fun i hi => lt_of_lt_of_le hi hjk)
  have hAne : A.Nonempty := hinf.nonempty
  haveI _ : Nonempty (Cardinal.mk A).ord.ToType := ⟨e.symm ⟨hAne.some, hAne.some_mem⟩⟩
  refine ⟨⟨Set.range E, Set.range_nonempty E, ?_⟩, ?_, ?_⟩
  · rintro _ ⟨j, rfl⟩ _ ⟨k, rfl⟩ _; rcases le_total j k with h | h
    · exact Or.inl (hEmono j k h)
    · exact Or.inr (hEmono k j h)
  · rintro _ ⟨j, rfl⟩; constructor
    · intro x hx; obtain ⟨i, _, rfl⟩ := hx; exact (e i).2
    · have h1 : Cardinal.mk (E j) = Cardinal.mk (Set.Iio j) :=
        Cardinal.mk_image_eq fun _ _ h ↦ e.injective (Subtype.ext h)
      rw [h1]; simpa using Cardinal.mk_Iio_lt j
  · intro a ha
    obtain ⟨k, hk⟩ := (Cardinal.noMaxOrder haleph).exists_gt (e.symm ⟨a, ha⟩)
    refine ⟨E k, ⟨k, rfl⟩, ?_⟩
    refine ⟨e.symm ⟨a, ha⟩, hk, ?_⟩
    simp only [Function.comp_apply, Equiv.apply_symm_apply]

/-
The set of `b`-images of finite subsets of `E` has cardinality below `κ` whenever `E` does and
`κ` is infinite.
-/
omit [ChainCompletePartialOrder α] in
lemma card_image_finsets_lt (b : Finset α → α) (E : Set α) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hE : Cardinal.mk E < κ) :
    Cardinal.mk (b '' {F : Finset α | ↑F ⊆ E}) < κ := by
  apply lt_of_le_of_lt (Cardinal.mk_le_mk_of_subset _) _
  · exact (Set.range fun f : Finset E => b ( f.map (Function.Embedding.subtype _))) ∪ { b ∅ }
  · rintro _ ⟨ F, hF, rfl ⟩ ; by_cases h : F = ∅ <;>
      simp_all only [mem_setOf_eq, Finset.coe_empty, empty_subset, union_singleton, mem_insert_iff,
        mem_range, true_or]
    refine Or.inr ⟨F.preimage ( fun x => x.val ) ?_, ?_⟩;
    · exact fun x hx y hy hxy => Subtype.ext hxy;
    · congr ; ext x ; aesop;
  · refine lt_of_le_of_lt ( Cardinal.mk_union_le _ _ ) ?_;
    refine lt_of_le_of_lt ( add_le_add ( Cardinal.mk_range_le ) le_rfl ) ?_;
    by_cases hE' : Infinite E <;>
      simp_all only [Cardinal.mk_finset_of_infinite, Cardinal.mk_fintype, Fintype.card_unique,
         Nat.cast_one, Cardinal.aleph0_le_mk, Cardinal.add_one_of_aleph0_le,
         not_infinite_iff_finite];
    refine lt_of_lt_of_le ?_ hκ;
    refine Cardinal.add_lt_aleph0 (@Cardinal.lt_aleph0_of_finite _ ?_) Cardinal.one_lt_aleph0
    exact (@Finset.fintype _ (@Fintype.ofFinite _ hE')).finite


/-- **Iwamura's lemma.** An infinite directed set `A` is the "union" of a `⊆`-chain of directed
subsets, each of cardinality strictly smaller than `A`, in the sense that every element of `A` is
dominated by an element of one of the subsets. -/
lemma exists_chain_of_small_directed (A : DSet α) (hinf : A.carrier.Infinite) :
    ∃ 𝔄 : NonemptyChain (DSet α),
      (∀ B ∈ 𝔄, B ⊆ A ∧ Cardinal.mk B < Cardinal.mk A) ∧
      (∀ a ∈ A, ∃ B ∈ 𝔄, ∃ y ∈ B, a ≤ y) := by
  classical
  have hκ : Cardinal.aleph0 ≤ Cardinal.mk A := Cardinal.aleph0_le_mk_iff.mpr hinf.to_subtype
  obtain ⟨b, hb1, hb2, hb3⟩ := exists_mono_ub A
  obtain ⟨𝔈, hsub, hcov⟩ := exists_filtration A.carrier hinf
  refine ⟨
    NonemptyChain.mk
      (Set.range fun E : ↑𝔈.carrier ↦ ⟨b '' {F : Finset α | ↑F ⊆ E.val}, ?_, ?_⟩) ?_ ?_,
    ?_, ?_⟩
  · have hEA := (hsub _ E.property).1
    rintro _ ⟨F, hF, rfl⟩ _ ⟨G, hG, rfl⟩
    have hFGE : ↑(F ∪ G) ⊆ E.val := by
      rw [Finset.coe_union]; exact Set.union_subset hF hG
    have hFGA : ↑(F ∪ G) ⊆ A.carrier := hFGE.trans hEA
    simp only [mem_image, mem_setOf_eq, exists_exists_and_eq_and]
    refine ⟨F ∪ G, hFGE, ?_, ?_⟩
    · exact hb3 _ _ (le_trans hF hEA) hFGA Finset.subset_union_left
    · exact hb3 _ _ (le_trans hG hEA) hFGA Finset.subset_union_right
  · refine Set.image_nonempty.mpr ⟨∅, ?_⟩
    simp only [mem_setOf_eq, Finset.coe_empty, empty_subset]
  · refine @range_nonempty _ _ 𝔈.Nonempty'.to_subtype _
  · -- `𝔄` is a `⊆`-chain (images of a nested family of finset-collections)
    rintro _ ⟨⟨E₁, hE₁⟩, rfl⟩ _ ⟨⟨E₂, hE₂⟩, rfl⟩ _
    rcases 𝔈.isChain'.total hE₁ hE₂ with h | h
    · exact Or.inl (Set.image_mono (fun F hF => le_trans hF h))
    · exact Or.inr (Set.image_mono (fun F hF => le_trans hF h))
  · -- each member is a directed subset of `A` of smaller cardinality
    rintro _ ⟨⟨E, hE⟩, rfl⟩
    have hEA : ↑E ⊆ A.carrier := (hsub E hE).1
    refine ⟨?_, ?_⟩
    · exact Set.image_subset_iff.mpr fun F hF => hb1 F (hF.trans hEA)
    · exact card_image_finsets_lt b E hκ (hsub E hE).2
  · -- every element of `A` is dominated inside one of the members
    intro a ha
    obtain ⟨E, hE, haE⟩ := hcov a ha
    have haE' : (↑({a} : Finset α) : Set α) ⊆ E := by
      rw [Finset.coe_singleton, Set.singleton_subset_iff]; exact haE
    refine ⟨?_, ?_, b {a}, ?_, ?_⟩
    rotate_left
    · refine Set.mem_range.mpr ⟨⟨E, hE⟩, ?_⟩; rfl
    · exact Set.mem_image_of_mem _ haE'
    · exact hb2 {a} (haE'.trans (hsub E hE).1) a (Finset.mem_singleton_self a)

/-
The infinite case of Markowsky's theorem: assuming the statement for all directed sets of
strictly smaller cardinality (`IH`), an infinite directed set has a least upper bound.
-/
lemma isLUB_of_infinite_directed (A : DSet α) (hinf : A.carrier.Infinite)
    (IH : ∀ B : DSet α, Cardinal.mk B < Cardinal.mk A → ∃ s, IsLUB B.carrier s) :
    ∃ s, IsLUB A.carrier s := by
  obtain ⟨𝔄, hchain, hcover⟩ := exists_chain_of_small_directed A hinf;
  -- For each `B ∈ 𝔄`, `IH B (card bound) (directedness)` gives a least upper bound of `B`.
  refine ⟨(NonemptyChain.mk {c : α | ∃ B ∈ 𝔄, IsLUB B c} ?_ ?_).cSup, ?_⟩
  · have ⟨d, hd⟩ := 𝔄.Nonempty'
    have ⟨x, hx⟩ := IH d (hchain _ hd).2
    exact ⟨x, d, hd, hx⟩
  · rintro c₁ ⟨ B₁, hB₁, hB₁' ⟩ c₂ ⟨ B₂, hB₂, hB₂' ⟩
    cases 𝔄.isChain'.total hB₁ hB₂ <;> simp_all only [ne_eq] ;
    · exact fun h => Or.inl ( hB₁'.2 fun x hx => hB₂'.1 ( by tauto ) );
    · exact fun h => Or.inr ( hB₂'.2 <| fun x hx => hB₁'.1 <| by tauto );
  · refine isLUB_of_chain_dominating A.carrier _ ?_ ?_
    · intro a ha; rcases hcover a ha with ⟨ B, hB, y, hy, hay ⟩
      obtain ⟨ s, hs ⟩ := IH B (hchain _ hB).2
      exact ⟨ s, ⟨ B, hB, hs ⟩, hay.trans ( hs.1 hy ) ⟩
    · rintro _ ⟨ B, hB, hB' ⟩ u hu
      refine hB'.2 ?_; intro x hx; exact hu ((hchain _ hB).1 hx)

/-- **Markowsky's theorem, key direction.** In a chain-complete poset every directed set has a
least upper bound. Proved by strong induction on cardinality. -/
theorem isLUB_of_directed_of_chainComplete (A : DSet α) : ∃ s, IsLUB A.carrier s := by
  suffices H : ∀ κ : Cardinal, ∀ A : DSet α, Cardinal.mk A = κ → ∃ s, IsLUB A.carrier s by
    exact H _ A rfl
  intro κ
  induction κ using WellFoundedLT.induction with
  | _ κ IH =>
    intro A hκ
    by_cases hfin : A.carrier.Finite
    · have ⟨x, hx, hub⟩ := A.finite_upper_bound (le_refl _) hfin
      refine ⟨x, hub, ?_⟩; intro y hy; exact hy hx
    · refine isLUB_of_infinite_directed A hfin ?_
      intro B hB; exact IH (Cardinal.mk B) (hκ ▸ hB) B rfl

end Markowsky

namespace DCPO

/-- Construct a DCPO from a ChainCompletePartialOrder
-/
@[reducible]
noncomputable def of_ChainCompletePartialOrder {α : Type*} (c : ChainCompletePartialOrder α) :
    DCPO α where
  dSup d := (isLUB_of_directed_of_chainComplete d).choose
  lubOfDirected d := (isLUB_of_directed_of_chainComplete d).choose_spec

end DCPO

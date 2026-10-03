import Appendix
open Set MeasureTheory
namespace Asakura

/-- The three lambda-system axioms as printed in A.1. -/
structure ManuscriptLambda {Ω : Type*} (L : Set (Set Ω)) : Prop where
  univ_mem : Set.univ ∈ L
  diff_mem : ∀ {A B}, A ∈ L → B ∈ L → A ⊆ B → B \ A ∈ L
  increasing_union : ∀ A : ℕ → Set Ω, (∀ n, A n ∈ L) → Monotone A → (⋃ n, A n) ∈ L

lemma ManuscriptLambda.compl_mem {Ω : Type*} {L : Set (Set Ω)} (h : ManuscriptLambda L)
    {A : Set Ω} (hA : A ∈ L) : Aᶜ ∈ L := by
  have heq : (Set.univ : Set Ω) \ A = Aᶜ := by ext x; simp
  rw [← heq]
  exact h.diff_mem hA h.univ_mem (Set.subset_univ A)

lemma ManuscriptLambda.empty_mem {Ω : Type*} {L : Set (Set Ω)} (h : ManuscriptLambda L) :
    ∅ ∈ L := by simpa using h.compl_mem h.univ_mem

lemma ManuscriptLambda.disjoint_union {Ω : Type*} {L : Set (Set Ω)}
    (h : ManuscriptLambda L) {A B : Set Ω} (hA : A ∈ L) (hB : B ∈ L)
    (hd : Disjoint A B) : A ∪ B ∈ L := by
  have hsub : B ⊆ Aᶜ := by
    intro x hxB hxA
    exact Set.disjoint_left.mp hd hxA hxB
  have heq : (Aᶜ \ B)ᶜ = A ∪ B := by classical
                                           ext x; simp; tauto
  rw [← heq]
  exact h.compl_mem (h.diff_mem hB (h.compl_mem hA) hsub)

/-- Conversion of the manuscript's convention to Mathlib's Dynkin-system convention. -/
def ManuscriptLambda.toDynkin {Ω : Type*} {L : Set (Set Ω)} (h : ManuscriptLambda L) :
    MeasurableSpace.DynkinSystem Ω where
  Has := (· ∈ L)
  has_empty := h.empty_mem
  has_compl := h.compl_mem
  has_iUnion_nat := by
    intro f hd hf
    have hfin : ∀ s : Finset ℕ, (⋃ i ∈ s, f i) ∈ L := by
      intro s
      induction s using Finset.induction_on with
      | empty => simpa using h.empty_mem
      | @insert a s ha ih =>
        rw [Finset.set_biUnion_insert]
        apply h.disjoint_union (hf a) ih
        apply Set.disjoint_iUnion_right.mpr
        intro b
        apply Set.disjoint_iUnion_right.mpr
        intro hb
        exact hd (by intro he; exact ha (he ▸ hb))
    have hu := h.increasing_union (fun n => ⋃ i ∈ Finset.range n, f i)
      (fun n => hfin _) (by
        intro n m hnm
        intro x hx
        rcases Set.mem_iUnion.mp hx with ⟨i, hi⟩
        rcases Set.mem_iUnion.mp hi with ⟨hi, hx⟩
        exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr
          ⟨Finset.mem_range.mpr ((Finset.mem_range.mp hi).trans_le hnm), hx⟩⟩)
    have heq : (⋃ n, ⋃ i ∈ Finset.range n, f i) = ⋃ i, f i := by
      ext x
      simp only [Set.mem_iUnion]
      constructor
      · rintro ⟨n, i, hi, hx⟩; exact ⟨i, hx⟩
      · rintro ⟨i, hx⟩; exact ⟨i + 1, i, Finset.mem_range.mpr (Nat.lt_succ_self i), hx⟩
    rwa [heq] at hu

/-- A.1 pi-lambda theorem with exactly the manuscript's lambda axioms. -/
theorem manuscript_pi_lambda {Ω : Type*} (P L : Set (Set Ω))
    (hP : IsPiSystem P) (hL : ManuscriptLambda L) (hPL : P ⊆ L) :
    ∀ A, MeasurableSet[MeasurableSpace.generateFrom P] A → A ∈ L := by
  intro A hA
  exact pi_lambda P hP hL.toDynkin hPL A hA

/-- A.1 lemma: pi plus lambda is a sigma algebra. -/
theorem manuscript_pi_lambda_sigma {Ω : Type*} (L : Set (Set Ω))
    (hP : IsPiSystem L) (hL : ManuscriptLambda L) :
    ∃ m : MeasurableSpace Ω, ∀ A, MeasurableSet[m] A ↔ A ∈ L := by
  refine ⟨MeasurableSpace.generateFrom L, fun A => ⟨?_, ?_⟩⟩
  · exact manuscript_pi_lambda L L hP hL (fun _ h => h) A
  · exact MeasurableSpace.measurableSet_generateFrom
end Asakura

import FullAuditDyadicCeil
import FullAuditStoppedContinuous

open MeasureTheory Set Filter Function
open scoped Topology
namespace Asakura.FullAudit
open Asakura.Chapter1Written

/-- Disjoint stopping-time fibers prove the constant conditional mean of a
bounded future test. This is the countable sum in the strong Markov proof. -/
theorem countable_future_test_integral {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : ℕ → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ i, F i ≤ m)
    (κ : Ω → ℕ) (hκ : ∀ i, MeasurableSet[F i] {ω | κ ω ≤ i})
    (U : ℕ → Ω → ℝ) (hU : ∀ i, Measurable[m] (U i)) (C c : ℝ)
    (hb : ∀ i ω, ‖U i ω‖ ≤ C) (hCE : ∀ i, P[U i | F i] =ᵐ[P] fun _ => c)
    (A : Set Ω) (hA : MeasurableSet[writtenStoppedSpace m F κ hκ] A) :
    (∫ ω in A, U (κ ω) ω ∂P) = ∫ _ in A, c ∂P := by
  let E : ℕ → Set Ω := fun i => {ω | κ ω = i}
  have hEm : ∀ i, MeasurableSet[m] (E i) := fun i =>
    hle i _ (countable_stopping_fiber F hF κ hκ i)
  have hUm : Measurable[m] (fun ω => U (κ ω) ω) := by
    intro B hB
    have he : (fun ω => U (κ ω) ω) ⁻¹' B = ⋃ i, E i ∩ (U i ⁻¹' B) := by
      ext ω
      simp only [mem_preimage,mem_iUnion,mem_inter_iff,E,mem_setOf_eq]
      constructor
      · intro h; exact ⟨κ ω,rfl,h⟩
      · rintro ⟨i,hi,h⟩; simpa only [hi] using h
    rw [he]
    exact MeasurableSet.iUnion fun i => (hEm i).inter (hU i hB)
  have hUi : Integrable (fun ω => U (κ ω) ω) P :=
    Integrable.of_bound hUm.aestronglyMeasurable C (ae_of_all _ fun ω => hb (κ ω) ω)
  have hAF : ∀ i, MeasurableSet[F i] (A ∩ E i) := fun i => stopped_event_fiber m F hF κ hκ hA i
  have hAFm : ∀ i, MeasurableSet[m] (A ∩ E i) := fun i => hle i _ (hAF i)
  have hd : Pairwise (Disjoint on (fun i => A ∩ E i)) := by
    intro i j hij
    exact disjoint_left.mpr fun ω hi hj => hij (hi.2.symm.trans hj.2)
  have hu : (⋃ i, A ∩ E i) = A := by ext ω; simp [E]
  rw [← hu,integral_iUnion hAFm hd hUi.integrableOn,
    integral_iUnion hAFm hd (integrable_const c).integrableOn]
  apply tsum_congr
  intro i
  have he : (fun ω => U (κ ω) ω) =ᵐ[P.restrict (A ∩ E i)] U i :=
    (ae_restrict_mem (hAFm i)).mono fun ω hω => by
      have hi : κ ω = i := hω.2
      simp only [hi]
  rw [integral_congr_ae he,← setIntegral_condExp (hle i)
    (Integrable.of_bound (hU i).aestronglyMeasurable C (ae_of_all _ (hb i))) (hAF i)]
  exact integral_congr_ae (ae_restrict_of_ae (hCE i))
end Asakura.FullAudit

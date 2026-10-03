import Chapter8DeterministicVectorItoLaw

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal
namespace Asakura.Chapter8
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter6
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

/-- Ito isometry for an actual deterministic vector-noise integral,
without a nondegeneracy assumption on its coefficient. -/
theorem deterministic_ito_projection_second_moment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d p : ℕ} (B : BrownianSystem P d)
    (G : Fin p → Fin d → ℝ → ℝ) (hG : ∀ i j,Continuous (G i j))
    (N : Fin p → Fin d → HalfClosedTime → Ω → ℝ)
    (hN : ∀ i j,LocalMProcessWitness P B.F (N i j))
    (hNI : ∀ i j,ItoCovarianceFormula P B.F (B.W j) (fun z => G i j z.2) (N i j))
    (v : Fin p → ℝ) (R : ℝ) (hR : 0≤R) :
    MemLp (fun w => ∑ i,v i*(∑ j,N i j (realTimeClamp R) w)) 2 P ∧
      (∫ w,(∑ i,v i*(∑ j,N i j (realTimeClamp R) w))^2 ∂P)=
        ∫ r in 0..R,∑ j,(∑ i,v i*G i j r)^2 := by
  have hl := deterministic_vector_ito_projection_law P B G hG N hN hNI v R hR
  have h2 := memLp_id_gaussianReal (μ := 0) (v := (⟨∫ r in 0..R,∑ j,(∑ i,v i*G i j r)^2,
    intervalIntegral.integral_nonneg_of_forall hR (fun _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))⟩ : ℝ≥0)) (p := 2)
  constructor
  · exact hl.memLp h2
  · have he := variance_id_gaussianReal (μ := 0) (v := (⟨∫ r in 0..R,∑ j,(∑ i,v i*G i j r)^2,
      intervalIntegral.integral_nonneg_of_forall hR (fun _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))⟩ : ℝ≥0))
    rw [variance_eq_integral measurable_id.aemeasurable] at he
    simp only [integral_id_gaussianReal,id_eq,sub_zero] at he
    exact (hl.integral_comp (by fun_prop : AEStronglyMeasurable (fun x : ℝ => x^2) _)).trans he
end Asakura.Chapter8

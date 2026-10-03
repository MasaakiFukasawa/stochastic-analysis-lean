import Chapter8DeterministicVectorItoLaw
import Chapter8BrownianForcingPath
import FullAuditGaussianIndependence

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal
namespace Asakura.Chapter10
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter6 Asakura.Chapter8
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- Actual deterministic vector Ito integrals have a joint Gaussian law, with
no invertibility assumption on the coefficient matrix. -/
theorem deterministic_integral_joint_gaussian {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d p : ℕ} (B : BrownianSystem P d)
    (G : Fin p → Fin d → ℝ → ℝ) (hG : ∀ i j,Continuous (G i j))
    (N : Fin p → Fin d → HalfClosedTime → Ω → ℝ)
    (hN : ∀ i j,LocalMProcessWitness P B.F (N i j))
    (hNI : ∀ i j,ItoCovarianceFormula P B.F (B.W j) (fun z => G i j z.2) (N i j))
    (R : ℝ) (hR : 0≤R) :
    HasGaussianLaw (fun w i => ∑ j,N i j (realTimeClamp R) w) P := by
  classical
  let X := fun w i => ∑ j,N i j (realTimeClamp R) w
  have hm : Measurable X := Measurable.of_eval (fun i => Finset.measurable_sum _
    (fun j _ => ((hN i j).adapted P B.F _ (half_real_time_finite R)).mono (B.le _) le_rfl))
  refine ⟨hm.aemeasurable,?_⟩
  apply isGaussian_of_map_eq_gaussianReal
  intro L
  let v := fun i => L (Pi.single i 1)
  have hrepr (x : Fin p → ℝ) : L x=∑ i,v i*x i := by
    have hx : x=∑ i,x i • Pi.single i (1:ℝ) := by
      ext j
      simp [Pi.single_apply,Finset.sum_apply]
    calc
      L x = L (∑ i,x i • Pi.single i (1:ℝ)) := congrArg L hx
      _ = ∑ i,v i*x i := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro i _
        simp only [map_smul,smul_eq_mul,v,mul_comm]
  have hl := deterministic_vector_ito_projection_law P B G hG N hN hNI v R hR
  refine ⟨0,⟨∫ r in 0..R,∑ j,(∑ i,v i*G i j r)^2,
    intervalIntegral.integral_nonneg_of_forall hR (fun _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))⟩,?_⟩
  rw [Measure.map_map L.continuous.measurable hm]
  have he : L ∘ X=(fun w => ∑ i,v i*(∑ j,N i j (realTimeClamp R) w)) := by
    funext w
    exact hrepr (X w)
  rw [he]
  exact hl.map_eq

end Asakura.Chapter10

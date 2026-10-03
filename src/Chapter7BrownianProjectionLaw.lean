import Chapter4BrownianSystem
import Chapter4VectorLevyConstructed

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal BigOperators
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter3Complete
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false

/-- Every scalar projection of the actual vector Brownian increment has the
stated Gaussian law and is independent of the past, also at zero variance. -/
theorem brownian_projection_law {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) (u : Fin d → ℝ) :
    let X := fun w => ∑ i,u i*(B.W i (realTimeClamp t) w-B.W i (realTimeClamp s) w)
    HasLaw X (gaussianReal 0 ⟨(t-s)*(∑ i,u i^2),
      mul_nonneg (sub_nonneg.mpr hst) (Finset.sum_nonneg (fun _ _ => sq_nonneg _))⟩) P ∧
    Indep (MeasurableSpace.comap X inferInstance) (B.F (realTimeClamp s)) P := by
  classical
  dsimp only
  have hm : Measurable (fun w => ∑ i,u i*(B.W i (realTimeClamp t) w-B.W i (realTimeClamp s) w)) :=
    Finset.measurable_sum _ (fun i _ => measurable_const.mul
      (((B.martingale i).adapted P B.F _ (real_time_below t (hs.trans hst) (EReal.coe_lt_top _))).mono (B.le _) le_rfl |>.sub
      (((B.martingale i).adapted P B.F _ (real_time_below s hs (EReal.coe_lt_top _))).mono (B.le _) le_rfl)))
  apply gaussian_independent_of_conditional_characteristic P _ (B.le _) _ hm
  intro z
  have hc := vector_levy_conditional_characteristic P (show (0:EReal)<⊤ by simp)
    B.F B.mono B.le B.null B.W B.C B.martingale B.cov
    (fun i j w r hr _ => B.clock i j w r hr) t (hs.trans hst) (EReal.coe_lt_top _)
    s ⟨hs,hst⟩ (fun i => z*u i)
  have he : (∑ i,(z*u i)^2)=z^2*(∑ i,u i^2) := by simp only [mul_pow,Finset.mul_sum]
  rw [he] at hc
  convert hc using 1
  · congr 1
    funext w
    congr 1
    rw [← Complex.ofReal_mul]
    congr 1
    rw [Finset.mul_sum]
    simp only [mul_assoc]
  · funext w
    congr 1
    simp only [NNReal.toReal,NNReal.coe_mk]
    push_cast
    ring

end Asakura.Chapter7

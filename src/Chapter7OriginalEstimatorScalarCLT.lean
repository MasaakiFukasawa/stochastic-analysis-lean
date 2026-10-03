import Chapter7BrownianMatrixScalarCLT
import Chapter7MatrixDriftNegligible
import Chapter7DriftEstimatorMeasurable

open MeasureTheory ProbabilityTheory Matrix Set Filter Finset
open scoped Topology BigOperators
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

theorem original_estimator_scalar_clt {Ω Γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Γ]
    (P : Measure Ω) (Q : Measure Γ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {d : ℕ} (B : BrownianSystem P d) (Baux : BrownianSystem Q 1)
    (H S : Matrix (Fin d) (Fin d) ℝ) (hH : H.transpose=H)
    (T K : ℝ) (hT : 0<T) (hK : 0≤K) (b : Fin d → ℝ → Ω → ℝ) (x : Fin d → Ω → ℝ)
    (hbc : ∀ i w,Continuous (fun r => b i r w))
    (hba : ∀ i r,r∈Icc 0 T → Measurable[B.F (realTimeClamp r)] (b i r))
    (hbb : ∀ i r,r∈Icc 0 T → ∀ w,|b i r w|≤K) (hx : ∀ i,Measurable (x i)) :
    TendstoInDistribution (fun n w => Real.sqrt ((n+1:ℕ):ℝ)*
      (∑ i,∑ j,H i j*(realizedProcessEntry (driftedProjectionProcess B (S i) (b i) (x i))
        (driftedProjectionProcess B (S j) (b j) (x j)) T (n+1) w-(S*S.transpose) i j))) atTop
      (fun g : EuclideanSpace ℝ (Fin d × Fin d) => ∑ i,∑ j,H i j*g (i,j))
      (fun _ => P) (estimatorGaussianLaw S) := by
  have hlim := brownian_matrix_scalar_clt P Q B Baux H S hH T hT
  have herr := matrix_drift_negligible P B H S T K hT hK b x hbc hba hbb
  apply tendstoInDistribution_of_tendstoInMeasure_sub _ _ hlim
  · apply herr.congr_left
    intro n
    apply ae_of_all
    intro w
    simp only [Pi.sub_apply,mul_sub,mul_sum,sum_sub_distrib]
    ring
  · intro n
    apply Measurable.aemeasurable
    apply measurable_const.mul
    apply Finset.measurable_sum
    intro i _
    apply Finset.measurable_sum
    intro j _
    apply measurable_const.mul
    apply Measurable.sub_const
    apply realized_process_entry_measurable _ _ T hT
    · intro t ht
      exact drifted_projection_measurable B (S i) (b i) (x i) T hT.le
        (fun w => (hbc i w).continuousOn) (fun r hr => (hba i r hr).mono (B.le _) le_rfl) (hx i) t ht
    · intro t ht
      exact drifted_projection_measurable B (S j) (b j) (x j) T hT.le
        (fun w => (hbc j w).continuousOn) (fun r hr => (hba j r hr).mono (B.le _) le_rfl) (hx j) t ht

end Asakura.Chapter7

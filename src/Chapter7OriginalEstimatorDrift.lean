import Chapter7DriftedProjectionIncrement
import Chapter7BrownianEstimatorConsistency

open MeasureTheory Set Filter Finset
open scoped Topology BigOperators
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- Drift removal for the estimator defined from actual observed levels. -/
theorem original_estimator_drift_negligible {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (u v : Fin d → ℝ) (T K : ℝ) (hT : 0<T) (hK : 0≤K) (b c : ℝ → Ω → ℝ) (x y : Ω → ℝ)
    (hbc : ∀ w,Continuous (fun r => b r w)) (hcc : ∀ w,Continuous (fun r => c r w))
    (hba : ∀ r∈Icc 0 T,Measurable[B.F (realTimeClamp r)] (b r))
    (hca : ∀ r∈Icc 0 T,Measurable[B.F (realTimeClamp r)] (c r))
    (hbb : ∀ r∈Icc 0 T,∀ w,|b r w|≤K) (hcb : ∀ r∈Icc 0 T,∀ w,|c r w|≤K) :
    TendstoInMeasure P (fun n w => Real.sqrt ((n+1:ℕ):ℝ)*
      (realizedProcessEntry (driftedProjectionProcess B u b x) (driftedProjectionProcess B v c y) T (n+1) w-
        realizedCovarianceEntry B u v T (n+1) w)) atTop (fun _ => 0) := by
  have hp := drift_covariance_entry_negligible P B u v T K hT hK b c hbc hcc hba hca hbb hcb
  apply hp.congr_left
  intro n
  apply ae_of_all
  intro w
  simp only [realizedProcessEntry,realizedCovarianceEntry,
    drifted_projection_increment B u b x hbc,drifted_projection_increment B v c y hcc,
    Nat.cast_add,Nat.cast_one]
  ring

end Asakura.Chapter7

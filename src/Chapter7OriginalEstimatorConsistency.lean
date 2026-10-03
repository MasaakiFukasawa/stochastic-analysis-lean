import Chapter7OriginalEstimatorDrift
import Chapter7ConsistencyTransfer

open MeasureTheory Set Filter Finset
open scoped Topology BigOperators
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4
set_option backward.isDefEq.respectTransparency false

theorem original_estimator_entry_consistency {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (u v : Fin d → ℝ) (T K : ℝ) (hT : 0<T) (hK : 0≤K) (b c : ℝ → Ω → ℝ) (x y : Ω → ℝ)
    (hbc : ∀ w,Continuous (fun r => b r w)) (hcc : ∀ w,Continuous (fun r => c r w))
    (hba : ∀ r∈Icc 0 T,Measurable[B.F (realTimeClamp r)] (b r))
    (hca : ∀ r∈Icc 0 T,Measurable[B.F (realTimeClamp r)] (c r))
    (hbb : ∀ r∈Icc 0 T,∀ w,|b r w|≤K) (hcb : ∀ r∈Icc 0 T,∀ w,|c r w|≤K) :
    TendstoInMeasure P (fun n => realizedProcessEntry (driftedProjectionProcess B u b x)
      (driftedProjectionProcess B v c y) T (n+1)) atTop (fun _ => ∑ j,u j*v j) := by
  exact consistency_from_sqrt_error P _ _ _ (brownian_estimator_consistency P B u v T hT)
    (original_estimator_drift_negligible P B u v T K hT hK b c x y hbc hcc hba hca hbb hcb)

end Asakura.Chapter7

import Chapter7FiniteProbabilitySum
import Chapter7ProbabilityCentering

open MeasureTheory Filter
open scoped Topology
namespace Asakura.Chapter7

lemma consistency_from_sqrt_error {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X Y : ℕ → Ω → ℝ) (c : ℝ)
    (hY : TendstoInMeasure P Y atTop (fun _ => c))
    (hXY : TendstoInMeasure P (fun n w => Real.sqrt ((n+1:ℕ):ℝ)*(X n w-Y n w)) atTop (fun _ => 0)) :
    TendstoInMeasure P X atTop (fun _ => c) := by
  apply (probability_centering P X c).mpr
  have hp := probability_add_zero P _ _ (probability_unscale_sqrt P _ hXY) ((probability_centering P Y c).mp hY)
  exact hp.congr_left (fun n => ae_of_all P (fun w => by ring))

end Asakura.Chapter7

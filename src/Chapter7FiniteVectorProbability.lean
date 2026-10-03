import Chapter7FiniteProbabilitySum
import Chapter7OriginalEstimatorMatrixCLT

open MeasureTheory Filter Finset
open scoped Topology BigOperators
namespace Asakura.Chapter7
set_option maxHeartbeats 1000000

lemma euclidean_norm_le_sum_abs {ι : Type*} [Fintype ι] (v : EuclideanSpace ℝ ι) :
    ‖v‖≤∑ i,|v i| := by
  have hs := sum_sq_le_sq_sum_of_nonneg (s := (univ : Finset ι)) (fun i _ => abs_nonneg (v i))
  simp only [sq_abs,← EuclideanSpace.real_norm_sq_eq] at hs
  nlinarith [norm_nonneg v,sum_nonneg (s := univ) (fun i _ => abs_nonneg (v i))]

lemma probability_euclidean_of_coordinates {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsFiniteMeasure P] (X : ℕ → Ω → EuclideanSpace ℝ ι) (c : EuclideanSpace ℝ ι)
    (h : ∀ i,TendstoInMeasure P (fun n w => X n w i) atTop (fun _ => c i)) :
    TendstoInMeasure P X atTop (fun _ => c) := by
  have hi i : TendstoInMeasure P (fun n w => |X n w i-c i|) atTop (fun _ => 0) := by
    apply tendstoInMeasure_iff_dist.mpr
    intro ε hε
    simpa only [Real.dist_eq,sub_zero,abs_abs] using tendstoInMeasure_iff_dist.mp (h i) ε hε
  have hs := probability_finite_sum_zero P univ (fun i n w => |X n w i-c i|) (fun i _ => hi i)
  apply tendstoInMeasure_iff_norm.mpr
  intro ε hε
  have hh := tendstoInMeasure_iff_dist.mp hs ε hε
  simp only [Real.dist_eq,sub_zero] at hh
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hh (fun _ => bot_le)
  intro n
  apply measure_mono
  intro w hw
  exact (hw.trans (euclidean_norm_le_sum_abs (X n w-c))).trans (le_abs_self _)

end Asakura.Chapter7

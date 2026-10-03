import Chapter8L1Approximation
import Chapter6SquareMeanToL1

open MeasureTheory Filter
open scoped Topology
namespace Asakura.Chapter8
set_option backward.isDefEq.respectTransparency false

/-- Mean-square convergence implies convergence in probability to a
possibly random limit. -/
theorem probability_of_square_error {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (Y : Ω → ℝ)
    (hi : ∀ n,MemLp (fun w => Y w-X n w) 2 P)
    (hl : Tendsto (fun n => ∫ w,(Y w-X n w)^2 ∂P) atTop (𝓝 0)) :
    TendstoInMeasure P X atTop Y := by
  have hh := Asakura.Chapter6.square_mean_zero_implies_L1_zero P _ hi hl
  have hp := probability_of_l1_limit P atTop (fun n w => Y w-X n w) 0
    (fun n => by simpa only [sub_zero] using (hi n).integrable (by norm_num))
    (by simpa only [sub_zero,Real.norm_eq_abs] using hh)
  apply tendstoInMeasure_iff_dist.mpr
  intro ε hε
  have he := tendstoInMeasure_iff_dist.mp hp ε hε
  simpa only [Real.dist_eq,sub_zero,abs_sub_comm] using he
end Asakura.Chapter8

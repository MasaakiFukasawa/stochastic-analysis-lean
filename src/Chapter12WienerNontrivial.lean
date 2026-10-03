import Chapter12LpZeroExtension
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open MeasureTheory Set
open scoped ENNReal
namespace Asakura.Chapter12

/-- The deterministic time space is nonzero: the indicator of (0,1]
has norm one. -/
theorem half_line_L2_nontrivial : Nontrivial (Lp ℝ 2 (volume.restrict (Ioi (0:ℝ)))) := by
  let μ := volume.restrict (Ioi (0:ℝ))
  have hm : μ (Ioc (0:ℝ) 1) = 1 := by
    rw [Measure.restrict_apply measurableSet_Ioc]
    have he : Ioc (0:ℝ) 1 ∩ Ioi 0 = Ioc 0 1 := inter_eq_left.mpr (fun _ h => h.1)
    rw [he,Real.volume_Ioc]
    norm_num
  let f : Lp ℝ 2 μ := indicatorConstLp 2 measurableSet_Ioc (by rw [hm]; simp) (1:ℝ)
  apply nontrivial_of_ne f 0
  intro he
  have hn : ‖f‖ = 1 := by
    dsimp only [f]
    rw [norm_indicatorConstLp (by norm_num) (by norm_num)]
    simp [Measure.real,hm]
  rw [he,norm_zero] at hn
  exact zero_ne_one hn

end Asakura.Chapter12

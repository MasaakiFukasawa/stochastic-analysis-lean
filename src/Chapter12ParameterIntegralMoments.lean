import Chapter12AllFiniteMoments
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory Set
open scoped ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false

theorem parameter_integral_memLp {α Ω : Type*} [MeasurableSpace α] [MeasurableSpace Ω]
    (μ : Measure α) [IsFiniteMeasure μ] (P : Measure Ω) (p : ℝ≥0∞)
    (F : α × Ω → ℝ) (hm : Measurable F) (G : Ω → ℝ) (hG : MemLp G p P)
    (hb : ∀ w, ∀ x, ‖F (x,w)‖ ≤ ‖G w‖) :
    MemLp (fun w => ∫ x,F (x,w) ∂μ) p P := by
  have hg : MemLp (fun w => μ.real univ * ‖G w‖) p P := hG.norm.const_mul _
  apply hg.of_le
  · exact hm.stronglyMeasurable.integral_prod_left'.aestronglyMeasurable
  · apply ae_of_all
    intro w
    have h := norm_integral_le_of_norm_le_const (ae_of_all μ (hb w))
    rw [Real.norm_of_nonneg (mul_nonneg (measureReal_nonneg) (norm_nonneg _))]
    exact h.trans_eq (mul_comm _ _)

end Asakura.Chapter12

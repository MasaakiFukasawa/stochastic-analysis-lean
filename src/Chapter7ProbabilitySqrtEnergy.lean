import Chapter7ProbabilityProduct

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter7
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- The exact square-root-energy form of the drift remainder argument. -/
theorem probability_sqrt_energy {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X V : ℕ → Ω → ℝ)
    (hX : TendstoInMeasure P X atTop (fun _ => 0))
    (hm : ∀ n,Measurable (V n)) (hi : ∀ n,Integrable (V n) P)
    (hv : ∀ n w,0 ≤ V n w) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ n,(∫ w,V n w ∂P) ≤ C) :
    TendstoInMeasure P (fun n w => X n w*Real.sqrt (V n w)) atTop (fun _ => 0) := by
  have hbound n w : |Real.sqrt (V n w)| ≤ 1+V n w := by
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    nlinarith [Real.sq_sqrt (hv n w),sq_nonneg (Real.sqrt (V n w)-1)]
  have hsi n : Integrable (fun w => |Real.sqrt (V n w)|) P := by
    apply ((integrable_const 1).add (hi n)).mono'
      (by simpa only [Real.norm_eq_abs] using (hm n).sqrt.norm.aestronglyMeasurable)
    exact ae_of_all _ fun w => by simpa only [Real.norm_eq_abs,abs_abs,Pi.add_apply] using hbound n w
  apply probability_product_bounded_moment P X (fun n w => Real.sqrt (V n w)) hX hsi (1+C) (by positivity)
  intro n
  calc
    _ ≤ ∫ w,1+V n w ∂P := integral_mono (hsi n) ((integrable_const _).add (hi n)) (hbound n)
    _ ≤ 1+C := by rw [integral_add (integrable_const _) (hi n)]; simpa using add_le_add_left (hb n) 1

end Asakura.Chapter7

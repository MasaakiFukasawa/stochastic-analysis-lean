import Chapter5ConditionalCommonBounds
import Chapter5ExponentialPayoff

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter5

/-- The bounded exponential terminal payoff supplies the common strictly
positive bound required by the logarithmic Ito construction. -/
theorem exponential_conditional_common_bounds
    {Ω D : Type*} [MeasurableSpace Ω]
    [TopologicalSpace D] [TopologicalSpace.SeparableSpace D] [Nonempty D]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : D → MeasurableSpace Ω) (hle : ∀ t,F t ≤ ‹MeasurableSpace Ω›)
    (V : Ω → ℝ) (hV : Measurable V)
    (f : ℝ → ℝ) (hf : Measurable f) (B a : ℝ) (hbound : ∀ x,|f x| ≤ B)
    (X : D → Ω → ℝ) (hX : ∀ w,Continuous (fun t => X t w))
    (hCE : ∀ t,X t =ᵐ[P] P[(fun w => Real.exp (a*f (V w)))|F t]) :
    0 < Real.exp (-|a| * B) ∧
    ∀ᵐ w ∂P,∀ t,Real.exp (-|a| * B) ≤ X t w ∧ X t w ≤ Real.exp (|a| * B) := by
  have hb w := exponential_payoff_bounds f B a hbound (V w)
  have hi : Integrable (fun w => Real.exp (a*f (V w))) P :=
    Integrable.of_bound ((measurable_const.mul (hf.comp hV)).exp.aestronglyMeasurable)
      (Real.exp (|a| * B)) (ae_of_all _ fun w => by
        simpa only [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] using (hb w).2)
  exact ⟨Real.exp_pos _,conditional_process_common_bounds P F hle _ hi X hX hCE
    _ _ (ae_of_all _ hb)⟩

/-- Dividing the representing integrand by a uniformly positive martingale
preserves L². This verifies the admissibility of the displayed Z. -/
theorem positive_quotient_memLp_two
    {S : Type*} [MeasurableSpace S] (ν : Measure S)
    (X G : S → ℝ) (hX : Measurable X) (hG : MemLp G 2 ν)
    (a b : ℝ) (ha : a ≠ 0) (hb : 0 < b) (hpos : ∀ᵐ s ∂ν,b ≤ X s) :
    MemLp (fun s => G s/(a*X s)) 2 ν ∧
      (fun s => a*X s*(G s/(a*X s))) =ᵐ[ν] G := by
  have hden : 0 < |a| * b := mul_pos (abs_pos.mpr ha) hb
  constructor
  · apply (hG.norm.const_smul ((|a| * b)⁻¹)).mono'
      ((hG.aestronglyMeasurable.aemeasurable.div (measurable_const.mul hX).aemeasurable).aestronglyMeasurable)
    filter_upwards [hpos] with s hs
    have hx : 0 < X s := hb.trans_le hs
    change ‖G s/(a*X s)‖ ≤ (|a| * b)⁻¹*‖G s‖
    simp only [norm_div,Real.norm_eq_abs,abs_mul,abs_of_pos hx]
    simpa only [smul_eq_mul,div_eq_mul_inv,mul_comm] using
      div_le_div_of_nonneg_left (abs_nonneg (G s)) hden (mul_le_mul_of_nonneg_left hs (abs_nonneg a))
  · filter_upwards [hpos] with s hs
    exact mul_div_cancel₀ _ (mul_ne_zero ha (ne_of_gt (hb.trans_le hs)))

end Asakura.Chapter5

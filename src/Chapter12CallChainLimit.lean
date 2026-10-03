import Chapter12ChainLimit
import Chapter12CallSmoothing

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false

/-- The derivative approximation at a kink converges in Lp precisely under
the no-atom condition used for the option payoffs. -/
theorem call_derivative_Lp_limit {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (p : ℝ≥0∞) (hp : 1 ≤ p) (hpt : p ≠ ∞)
    (F : Ω → ℝ) (hF : Measurable F) (K : ℝ) (hno : P {w | F w = K} = 0)
    (u : Ω → H) (hu : MemLp u p P)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεt : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun w => smoothCallSlope (ε n) K (F w) • u w-
      (if K < F w then (1:ℝ) else 0) • u w) p P) atTop (𝓝 0) := by
  have hm n : Measurable (fun z : ℝ => smoothCallSlope (ε n) K z) := by
    unfold smoothCallSlope
    fun_prop
  have hb : Measurable (fun z : ℝ => if K < z then (1:ℝ) else 0) := by
    change Measurable ((Ioi K).indicator (fun _ : ℝ => (1:ℝ)))
    exact measurable_const.indicator measurableSet_Ioi
  have hnot : ∀ᵐ w ∂P, F w ≠ K := by
    simpa only [ae_iff,not_not] using hno
  apply bounded_multiplier_Lp_limit P p hp hpt u hu _ _
    (fun n => ((hm n).comp hF).aestronglyMeasurable) (hb.comp hF).aestronglyMeasurable
    1 zero_le_one
  · intro n
    apply ae_of_all
    intro w
    have h := smoothCall_slope_bounds (ε n) K (F w) (hε n)
    dsimp only [Function.comp_def]
    rw [abs_of_nonneg h.1]
    exact h.2
  · exact ae_of_all _ fun w => by dsimp only [Function.comp_def]; split_ifs <;> norm_num
  · filter_upwards [hnot] with w hw
    exact smoothCall_slope_limit K (F w) hw ε hεt

end Asakura.Chapter12

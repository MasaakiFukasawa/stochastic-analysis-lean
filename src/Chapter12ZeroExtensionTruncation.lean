import Chapter12WienerTerminalMeasurable

open MeasureTheory Set Filter
open scoped ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/-- Truncation and the actual L2 zero extension commute. -/
theorem zero_extension_indicator {S : Type*} [MeasurableSpace S]
    (μ : Measure S) (A B : Set S) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (f : Lp ℝ 2 (μ.restrict A)) :
    L2ZeroExtension μ A hA ((Lp.memLp f).indicator hB |>.toLp (B.indicator (f : S → ℝ))) =
      ((Lp.memLp (L2ZeroExtension μ A hA f)).indicator hB).toLp
        (B.indicator (L2ZeroExtension μ A hA f : S → ℝ)) := by
  apply Lp.ext
  have hf := (ae_eq_restrict_iff_indicator_ae_eq hA).mp
    (((Lp.memLp f).indicator hB).coeFn_toLp)
  filter_upwards [L2ZeroExtension_coe μ A hA
      (((Lp.memLp f).indicator hB).toLp (B.indicator (f : S → ℝ))),hf,
    L2ZeroExtension_coe μ A hA f,
    ((Lp.memLp (L2ZeroExtension μ A hA f)).indicator hB).coeFn_toLp]
    with x hx hf hx0 hx1
  rw [hx,hf,hx1]
  by_cases hb : x ∈ B
  · rw [indicator_of_mem hb,hx0]
    by_cases ha : x ∈ A <;> simp [ha,hb]
  · by_cases ha : x ∈ A <;> simp [ha,hb]

end Asakura.Chapter12
#print axioms Asakura.Chapter12.zero_extension_indicator

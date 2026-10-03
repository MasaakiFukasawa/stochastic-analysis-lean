import Chapter13HJMPrimitive
import Mathlib.Analysis.Calculus.Deriv.Slope

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter13
set_option maxHeartbeats 1800000

/-- The terminal backward-looking rate converges to the left limit of the
short rate. No value prescribed at the jump time enters the limit. -/
theorem terminal_rate_left_limit (r:ℝ → ℝ) (T l:ℝ)
    (hm:StronglyMeasurableAtFilter r (𝓝[≤] T))
    (hl:Tendsto r (𝓝[≤] T ⊓ ae volume) (𝓝 l)) :
    Tendsto (fun s => (Real.exp (∫v in s..T,r v)-1)/(T-s)) (𝓝[<] T) (𝓝 l) := by
  have hd:HasDerivWithinAt (fun s => ∫v in s..T,r v) (-l) (Iio T) T :=
    (intervalIntegral.integral_hasDerivWithinAt_of_tendsto_ae_left
      (IntervalIntegrable.refl : IntervalIntegrable r volume T T) hm hl).mono Iio_subset_Iic_self
  have he:=hd.exp
  have he':HasDerivWithinAt (fun s => Real.exp (∫v in s..T,r v)) (-l) (Iio T) T := by
    simpa using he
  have hh: Tendsto (fun s => -slope (fun u => Real.exp (∫v in u..T,r v)) T s)
      (𝓝[<] T) (𝓝 l) := by
    simpa using ((hasDerivWithinAt_iff_tendsto_slope' (by simp : T∉Iio T)).mp he').neg
  convert hh using 1
  funext s
  simp only [slope_def_field,intervalIntegral.integral_same,Real.exp_zero]
  rw [← div_neg]
  congr 1
  ring
end Asakura.Chapter13
#print axioms Asakura.Chapter13.terminal_rate_left_limit

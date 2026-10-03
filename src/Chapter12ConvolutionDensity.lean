import Chapter12DensityApproximationLimit
import Mathlib.MeasureTheory.Group.LIntegral

open MeasureTheory MeasureTheory.Measure
open scoped ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

/-- A convolution with a density has the mixture density, even when the
first measure has no density. This is the Gaussian smoothing step. -/
theorem convolution_mixture_density {E : Type*}
    [AddCommGroup E] [MeasurableSpace E] [MeasurableAdd₂ E] [MeasurableNeg E]
    (μ ν : Measure E) [SFinite μ] [SFinite ν] [IsAddLeftInvariant ν]
    (g : E → ℝ≥0∞) (hg : Measurable g) :
    (μ.prod (ν.withDensity g)).map (fun z : E × E => z.1+z.2)=
      ν.withDensity (fun z => ∫⁻ x,g (z-x) ∂μ) := by
  refine Measure.ext_of_lintegral _ fun φ hφ => ?_
  rw [lintegral_map hφ (by fun_prop),lintegral_prod _ (by fun_prop),
    lintegral_withDensity_eq_lintegral_mul ν (by fun_prop) hφ]
  have hx (x : E) : (∫⁻ y,φ (x+y) ∂ν.withDensity g)=
      ∫⁻ z,g (z-x)*φ z ∂ν := by
    rw [lintegral_withDensity_eq_lintegral_mul ν hg (by fun_prop)]
    have ht := lintegral_add_left_eq_self (μ := ν) (fun z => g (z-x)*φ z) x
    simpa only [add_sub_cancel_left,Pi.mul_apply] using ht
  simp_rw [hx]
  rw [lintegral_lintegral_swap (by fun_prop)]
  apply lintegral_congr
  intro z
  exact lintegral_mul_const'' _ (by fun_prop)

end Asakura.Chapter12

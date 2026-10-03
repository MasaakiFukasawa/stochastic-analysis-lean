import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.HasLaw
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace Asakura

lemma gaussian_norm_scaling (v : ℝ≥0) (p : ℝ≥0∞) :
    eLpNorm id p (gaussianReal 0 v) =
      ENNReal.ofReal (Real.sqrt v) * eLpNorm id p (gaussianReal 0 1) := by
  have he : (gaussianReal 0 1).map (fun x : ℝ => Real.sqrt v * x) = gaussianReal 0 v := by
    rw [gaussianReal_map_const_mul]
    congr 1
    · ring
    · apply NNReal.coe_injective
      simp [Real.sq_sqrt v.coe_nonneg]
  rw [← he, eLpNorm_map_measure]
  · change eLpNorm (fun x : ℝ => Real.sqrt v * x) p (gaussianReal 0 1) = _
    change eLpNorm (Real.sqrt v • (id : ℝ → ℝ)) p (gaussianReal 0 1) = _
    rw [eLpNorm_const_smul, Real.enorm_eq_ofReal_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  all_goals fun_prop

lemma gaussian_increment_lp {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} {v : ℝ≥0} (hX : HasLaw X (gaussianReal 0 v) P) (p : ℝ≥0∞) :
    eLpNorm X p P = ENNReal.ofReal (Real.sqrt v) * eLpNorm id p (gaussianReal 0 1) := by
  rw [← gaussian_norm_scaling]
  rw [← hX.map_eq, eLpNorm_map_measure]
  · rfl
  all_goals fun_prop
end Asakura

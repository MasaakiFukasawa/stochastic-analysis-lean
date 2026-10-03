import GaussianMoments
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace Asakura
variable {Ω T : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

lemma fractional_increment_law (X : T → Ω → ℝ) (hG : IsGaussianProcess X P)
    (u : T → ℝ) (H : ℝ) (hH : 0 < H) (hm : ∀ t, (∫ ω, X t ω ∂P) = 0)
    (hc : ∀ s t, (∫ ω, X s ω * X t ω ∂P) =
      ((u s)^(2*H) + (u t)^(2*H) - |u s - u t|^(2*H))/2) (s t : T) :
    HasLaw (X s - X t) (gaussianReal 0 (Real.toNNReal (|u s-u t|^(2*H)))) P := by
  have hl (t : T) := (hG.hasGaussianLaw_eval t).memLp_two
  have hv (t : T) : Var[X t; P] = (u t)^(2*H) := by
    rw [variance_eq_sub (hl t), hm]
    have hh := hc t t
    simp only [sub_self, abs_zero, Real.zero_rpow (by positivity : (2*H) ≠ 0)] at hh
    simp only [pow_two, Pi.mul_apply, zero_mul, sub_zero]
    rw [hh]
    ring
  have hcov : cov[X s,X t;P] = ((u s)^(2*H)+(u t)^(2*H)-|u s-u t|^(2*H))/2 := by
    rw [covariance_eq_sub (hl s) (hl t), hm, hm, zero_mul, sub_zero]
    exact hc s t
  have hvar : Var[X s-X t;P] = |u s-u t|^(2*H) := by
    rw [variance_sub (hl s) (hl t), hv, hv, hcov]
    ring
  have hmean : (∫ ω, (X s-X t) ω ∂P) = 0 := by
    simp only [Pi.sub_apply]
    rw [integral_sub ((hl s).integrable (by norm_num)) ((hl t).integrable (by norm_num)),
      hm,hm,sub_self]
  refine ⟨hG.hasGaussianLaw_sub.aemeasurable,?_⟩
  rw [hG.hasGaussianLaw_sub.map_eq_gaussianReal,hmean,hvar]

lemma fractional_increment_norm (X : T → Ω → ℝ) (hG : IsGaussianProcess X P)
    (u : T → ℝ) (H : ℝ) (hH : 0 < H) (hm : ∀ t, (∫ ω, X t ω ∂P) = 0)
    (hc : ∀ s t, (∫ ω, X s ω * X t ω ∂P) =
      ((u s)^(2*H) + (u t)^(2*H) - |u s - u t|^(2*H))/2)
    (p : ℝ≥0) (s t : T) :
    eLpNorm (X s-X t) p P =
      ENNReal.ofReal (|u s-u t|^H) * eLpNorm id p (gaussianReal 0 1) := by
  rw [gaussian_increment_lp (fractional_increment_law X hG u H hH hm hc s t)]
  rw [Real.coe_toNNReal _ (by positivity), Real.sqrt_eq_rpow,
    ← Real.rpow_mul (abs_nonneg _)]
  congr 2
  ring
end Asakura

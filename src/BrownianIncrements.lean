import GaussianMoments
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic

open MeasureTheory ProbabilityTheory
namespace Asakura
variable {Ω T : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

lemma gaussian_brownian_increment_law (X : T → Ω → ℝ) (hG : IsGaussianProcess X P)
    (u : T → ℝ) (hm : ∀ t, (∫ ω, X t ω ∂P) = 0)
    (hc : ∀ s t, (∫ ω, X s ω * X t ω ∂P) = min (u s) (u t)) (s t : T) :
    HasLaw (X s - X t) (gaussianReal 0 (Real.toNNReal |u s - u t|)) P := by
  have hl (t : T) := (hG.hasGaussianLaw_eval t).memLp_two
  have hv (t : T) : Var[X t; P] = u t := by
    rw [variance_eq_sub (hl t), hm]
    simpa [pow_two] using hc t t
  have hcov : cov[X s, X t; P] = min (u s) (u t) := by
    rw [covariance_eq_sub (hl s) (hl t), hm, hm, zero_mul, sub_zero]
    exact hc s t
  have hvar : Var[X s - X t; P] = |u s - u t| := by
    rw [variance_sub (hl s) (hl t), hv, hv, hcov]
    rcases le_total (u s) (u t) with h | h
    · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]; ring
    · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]; ring
  have hmean : (∫ ω, (X s - X t) ω ∂P) = 0 := by
    simp only [Pi.sub_apply]
    rw [integral_sub ((hl s).integrable (by norm_num)) ((hl t).integrable (by norm_num)), hm, hm, sub_self]
  refine ⟨hG.hasGaussianLaw_sub.aemeasurable, ?_⟩
  rw [hG.hasGaussianLaw_sub.map_eq_gaussianReal, hmean, hvar]
end Asakura

import Chapter8OUStationary
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion

open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
namespace Asakura.Chapter8

/-- A nondegenerate Brownian transition on the line cannot preserve a
probability measure, even one without finite moments. -/
theorem brownian_no_invariant (π : Measure ℝ) [IsProbabilityMeasure π]
    (v : ℝ≥0) (hv : 0 < v) : π ∗ gaussianReal 0 v ≠ π := by
  intro he
  have hz (t : ℝ) (ht : t ≠ 0) : charFun π t = 0 := by
    have h := congrArg (fun μ : Measure ℝ => charFun μ t) he
    rw [charFun_conv] at h
    have hg : charFun (gaussianReal 0 v) t ≠ 1 := by
      intro hg
      have hn := congrArg norm hg
      rw [charFun_gaussianReal] at hn
      simp only [mul_zero, zero_mul, zero_sub, Complex.norm_exp, norm_one] at hn
      have hp : (0:ℝ) < (v:ℝ)*t^2/2 := by positivity
      have hr : (-(v:ℂ)*(t:ℂ)^2/2).re = -(v:ℝ)*t^2/2 := by simp [pow_two]
      have hn' : Real.exp (-(v:ℝ)*t^2/2) = 1 := by convert hn using 1 <;> simp [pow_two] <;> ring
      have := Real.exp_lt_one_iff.mpr (show -(v:ℝ)*t^2/2 < 0 by linarith)
      linarith
    have hh : charFun π t * (charFun (gaussianReal 0 v) t - 1) = 0 := by
      rw [mul_sub, mul_one,h,sub_self]
    exact (mul_eq_zero.mp hh).resolve_right (sub_ne_zero.mpr hg)
  have hlim := (continuous_charFun (μ := π)).continuousAt.tendsto.comp
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have heq : (fun n : ℕ => charFun π (1/((n:ℝ)+1))) = fun _ : ℕ => (0:ℂ) := by
    funext n
    exact hz _ (by positivity)
  change Tendsto (fun n : ℕ => charFun π (1/((n:ℝ)+1))) atTop (𝓝 (charFun π 0)) at hlim
  rw [heq] at hlim
  have hzero : charFun π 0 = 0 := tendsto_nhds_unique hlim tendsto_const_nhds
  simpa using hzero

/-- The same characteristic-function contradiction in arbitrary positive
finite dimension, at the single Brownian time t = 1. -/
theorem brownian_no_invariant_finite_dimensional {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
    (π : Measure E) [IsProbabilityMeasure π] : π ∗ stdGaussian E ≠ π := by
  intro he
  have hz (t : E) (ht : t ≠ 0) : charFun π t = 0 := by
    have h := congrArg (fun μ : Measure E => charFun μ t) he
    rw [charFun_conv] at h
    have hg : charFun (stdGaussian E) t ≠ 1 := by
      intro hg
      have hn := congrArg norm hg
      rw [charFun_stdGaussian,Complex.norm_exp] at hn
      have hn' : Real.exp (-‖t‖^2/2) = 1 := by
        convert hn using 1 <;> simp [pow_two] <;> ring
      have hp : 0 < ‖t‖ := norm_pos_iff.mpr ht
      have := Real.exp_lt_one_iff.mpr (show -‖t‖^2/2 < 0 by nlinarith)
      linarith
    have hh : charFun π t * (charFun (stdGaussian E) t - 1) = 0 := by
      rw [mul_sub,mul_one,h,sub_self]
    exact (mul_eq_zero.mp hh).resolve_right (sub_ne_zero.mpr hg)
  obtain ⟨v,hv⟩ := exists_ne (0:E)
  have ht : Tendsto (fun n : ℕ => (1/((n:ℝ)+1)) • v) atTop (𝓝 (0:E)) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).smul_const v
  have hlim := (continuous_charFun (μ := π)).continuousAt.tendsto.comp ht
  have heq : (charFun π ∘ fun n : ℕ => (1/((n:ℝ)+1)) • v) = fun _ : ℕ => (0:ℂ) := by
    funext n
    exact hz _ (smul_ne_zero (by positivity) hv)
  rw [heq] at hlim
  have hzero : charFun π 0 = 0 := tendsto_nhds_unique hlim tendsto_const_nhds
  simpa using hzero

end Asakura.Chapter8

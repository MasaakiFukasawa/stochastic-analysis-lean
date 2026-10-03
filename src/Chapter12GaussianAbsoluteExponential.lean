import Chapter12GaussianExponentialLp
import Chapter12FiniteGreekExponents

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

/-- Absolute-value exponential envelopes remain in every finite Lp under
a Gaussian law. This supplies domination without smoothness of the payoff. -/
theorem gaussian_abs_exponential_memLp {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Z : Ω → ℝ) (m : ℝ) (v : ℝ≥0)
    (hZ : HasLaw Z (gaussianReal m v) P) (a : ℝ)
    (p : ℝ≥0∞) (hp : p≠⊤) : MemLp (fun w => Real.exp (a*|Z w|)) p P := by
  have hi := (gaussian_exponential_memLp P Z m v hZ a p hp).add
    (gaussian_exponential_memLp P Z m v hZ (-a) p hp)
  apply hi.mono' ((Real.measurable_exp.comp_aemeasurable ((continuous_abs.measurable.comp_aemeasurable hZ.aemeasurable).const_mul a)).aestronglyMeasurable)
  filter_upwards [] with w
  change ‖Real.exp (a*|Z w|)‖≤Real.exp (a*Z w)+Real.exp (-a*Z w)
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  by_cases hw : 0≤Z w
  · rw [abs_of_nonneg hw]
    exact le_add_of_nonneg_right (Real.exp_nonneg _)
  · rw [abs_of_neg (lt_of_not_ge hw),mul_neg,← neg_mul]
    exact le_add_of_nonneg_left (Real.exp_nonneg _)

theorem gaussian_polynomial_envelope_memLp {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Z : Ω → ℝ) (m : ℝ) (v : ℝ≥0)
    (hZ : HasLaw Z (gaussianReal m v) P) (n : ℕ)
    (p : ℝ≥0∞) (hp : p≠⊤) : MemLp (fun w => (1+|Z w|)^n) p P := by
  have hP : IsProbabilityMeasure P := hZ.isProbabilityMeasure
  letI := hP
  by_cases hn : n=0
  · subst n
    simpa using (memLp_const (1:ℝ) (μ := P) (p := p))
  have hnp : (n : ℝ≥0∞)≠0 := by exact_mod_cast hn
  have hninf : (n : ℝ≥0∞)≠⊤ := by simp
  have hz : MemLp Z (p*n) P := by
    simpa using hZ.memLp_comp (memLp_id_gaussianReal' (p*n) (ENNReal.mul_ne_top hp hninf))
  have hb : MemLp (fun w => 1+|Z w|) (p*n) P := (memLp_const (1:ℝ)).add hz.norm
  have hpow := hb.norm_rpow_div (n : ℝ≥0∞)
  have he (w) : ‖1+|Z w|‖=1+|Z w| := Real.norm_of_nonneg (by positivity)
  simpa only [he,ENNReal.toReal_natCast,Real.rpow_natCast,ENNReal.mul_div_cancel_right hnp hninf] using hpow

/-- A square-integrable payoff times a Gaussian exponential-polynomial
score envelope is integrable, by Holder; no payoff derivative is assumed. -/
theorem gaussian_payoff_score_envelope_integrable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Z f : Ω → ℝ) (m : ℝ) (v : ℝ≥0)
    (hZ : HasLaw Z (gaussianReal m v) P) (hf : MemLp f 2 P) (a : ℝ) (n : ℕ) :
    Integrable (fun w => |f w| *Real.exp (a*|Z w|)*(1+|Z w|)^n) P := by
  have he := gaussian_abs_exponential_memLp P Z m v hZ a 4 (by norm_num)
  have hp := gaussian_polynomial_envelope_memLp P Z m v hZ n 4 (by norm_num)
  have hb : MemLp (fun w => Real.exp (a*|Z w|)*(1+|Z w|)^n) 2 P := he.mul hp
  convert hf.norm.integrable_mul hb using 1
  funext w
  simp only [Real.norm_eq_abs,Pi.mul_apply]
  ring

end Asakura.Chapter12

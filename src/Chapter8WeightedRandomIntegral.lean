import Chapter8RandomIntegralSquare
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

open MeasureTheory Set
open scoped ENNReal NNReal
namespace Asakura.Chapter8
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- Weighted Cauchy--Schwarz for a random integral: a uniform second-moment
bound is multiplied by the square of the kernel mass, not by its L2 mass. -/
theorem weighted_random_integral_bound {Ω A E : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (P : Measure Ω) [IsProbabilityMeasure P] (μ : Measure A)
    (k : A → ℝ≥0) (hk : Measurable k) (hki : (∫⁻ t,(k t:ℝ≥0∞) ∂μ)<∞)
    (H : Ω × A → E) (hH : Measurable H)
    (h2 : MemLp H 2 (P.prod (μ.withDensity (fun t => k t))))
    (C : ℝ) (hb : ∀ᵐ t ∂μ,(∫ w,‖H (w,t)‖^2 ∂P)≤C) :
    MemLp (fun w => ∫ t,(k t:ℝ) • H (w,t) ∂μ) 2 P ∧
      (∫ w,‖∫ t,(k t:ℝ) • H (w,t) ∂μ‖^2 ∂P)≤(∫ t,(k t:ℝ) ∂μ)^2*C := by
  let ν := μ.withDensity (fun t => k t)
  letI : IsFiniteMeasure ν := isFiniteMeasure_withDensity hki.ne
  have hb' : ∀ᵐ t ∂ν,(∫ w,‖H (w,t)‖^2 ∂P)≤C := (withDensity_absolutelyContinuous μ _).ae_le hb
  have hmass : ν.real univ=∫ t,(k t:ℝ) ∂μ := by
    have hh := integral_withDensity_eq_integral_smul hk (fun _ : A => (1:ℝ)) (μ := μ)
    simpa only [integral_const,smul_eq_mul,mul_one,NNReal.smul_def] using hh
  have hh := random_integral_square_bound P ν H hH h2 C hb'
  dsimp only [ν] at hh
  simp_rw [integral_withDensity_eq_integral_smul hk,NNReal.smul_def] at hh
  rw [hmass] at hh
  exact hh
end Asakura.Chapter8

import Chapter11EuropeanConditional
import Chapter11PayoffIntegrability
import Chapter4BlackScholesConstructed

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false

/-- The polynomial payoff's L2 hypothesis is verified for the actual
geometric Brownian terminal stock, for real growth exponents. -/
theorem european_actual_terminal_L2 {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (h : Ioi (0:ℝ) → ℝ) (hh : Continuous h) (C m : ℝ)
    (hb : ∀ x,‖h x‖≤C*(1+x.val^m)) (s a σ R : ℝ) (hs : 0<s) (hR : 0<R) :
    MemLp (fun w => h ⟨s*Real.exp (a*R+σ*B.W 0 (realTimeClamp R) w),mul_pos hs (Real.exp_pos _)⟩) 2 P := by
  let S : ℝ → Ioi (0:ℝ) := fun z => ⟨s*Real.exp (a*R+(σ*Real.sqrt R)*z),mul_pos hs (Real.exp_pos _)⟩
  have hS : Measurable S := (measurable_const.mul ((measurable_const.add (measurable_id.const_mul _)).exp)).subtype_mk
  have hp := polynomial_payoff_memLp_two (gaussianReal 0 1) S hS h hh C m hb
    (lognormal_real_moment_integrable s (a*R) (σ*Real.sqrt R) (2*m) hs)
  have hl := brownian_standardized_law P (T:=(⊤:EReal)) (by simp) B.F B.mono B.le B.null
    (B.W 0) (B.C 0 0) (B.martingale 0) (B.cov 0 0)
    (fun w t ht _ => B.diagonal_clock 0 w t ht) R hR (EReal.coe_lt_top R)
  have he w : S (B.W 0 (realTimeClamp R) w/Real.sqrt R)=
      (⟨s*Real.exp (a*R+σ*B.W 0 (realTimeClamp R) w),mul_pos hs (Real.exp_pos _)⟩ : Ioi (0:ℝ)) := by
    apply Subtype.ext
    dsimp only [S]
    congr 2
    field_simp [Real.sqrt_ne_zero'.mpr hR]
  simpa only [Function.comp_def,he] using hl.memLp_comp hp

/-- Positivity of the Gaussian price needs only positivity of the payoff. -/
theorem european_gaussian_price_nonnegative (h : Ioi (0:ℝ) → ℝ) (hn : ∀ x,0≤h x)
    (r σ θ x : ℝ) (hx : 0<x) :
    0≤Real.exp (-r*θ)*(∫ z,h ⟨x*Real.exp ((r-σ^2/2)*θ+σ*Real.sqrt θ*z),mul_pos hx (Real.exp_pos _)⟩ ∂gaussianReal 0 1) :=
  mul_nonneg (Real.exp_pos _).le (integral_nonneg fun z => hn _)

end Asakura.Chapter11

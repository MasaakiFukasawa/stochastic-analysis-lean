import Chapter4FeynmanKacLimits
import Chapter4GaussianPayoff

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal
namespace Asakura.Chapter11
open Asakura.Chapter4
set_option maxHeartbeats 2000000

/-- The exceptional terminal corner has probability zero, from the actual
Gaussian law, without imposing continuity of the payoff at the corner. -/
theorem lognormal_terminal_no_atom {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) (Z : Ω → ℝ) (hZ : HasLaw Z (gaussianReal 0 1) Q)
    (s a σ b : ℝ) (hs : 0<s) (hσ : σ≠0) (hb : 0<b) :
    Q {w | s*Real.exp (a+σ*Z w)=b}=0 := by
  have he : {w | s*Real.exp (a+σ*Z w)=b}={w | Z w=(Real.log (b/s)-a)/σ} := by
    ext w
    simp only [mem_setOf_eq]
    constructor
    · intro h
      have hx : Real.exp (a+σ*Z w)=b/s := (eq_div_iff hs.ne').mpr (by simpa only [mul_comm] using h)
      have hl := congrArg Real.log hx
      rw [Real.log_exp] at hl
      apply (eq_div_iff hσ).mpr
      linarith
    · intro h
      rw [h,show a+σ*((Real.log (b/s)-a)/σ)=Real.log (b/s) by field_simp;ring,
        Real.exp_log (div_pos hb hs)]
      field_simp
  rw [he,hZ.measure_eq (p:=fun z => z=(Real.log (b/s)-a)/σ) (measurableSet_singleton _)]
  letI := nullSingletonClass_gaussianReal (μ:=0) (v:=1) (by norm_num)
  exact measure_singleton _

/-- Bounded terminal convergence in the barrier argument implies L2
convergence, even though the corner is excluded only almost surely. -/
theorem bounded_terminal_L2 {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q] (Z : ℕ → Ω → ℝ) (Y : Ω → ℝ) (K : ℝ)
    (hZ : ∀ n,AEStronglyMeasurable (Z n) Q) (hY : AEStronglyMeasurable Y Q)
    (hb : ∀ n,∀ᵐ w ∂Q,|Z n w|≤K)
    (hc : ∀ᵐ w ∂Q,Tendsto (fun n => Z n w) atTop (𝓝 (Y w))) :
    Tendsto (fun n => ∫ w,(Z n w-Y w)^2 ∂Q) atTop (𝓝 0) := by
  have hy : ∀ᵐ w ∂Q,|Y w|≤K := by
    filter_upwards [hc,ae_all_iff.mpr hb] with w hw hb
    exact le_of_tendsto hw.abs (Eventually.of_forall hb)
  have hdom n : ∀ᵐ w ∂Q,‖(Z n w-Y w)^2‖≤4*K^2 := by
    filter_upwards [hb n,hy] with w hz hy
    rw [Real.norm_eq_abs,abs_sq]
    have hz' := abs_le.mp hz
    have hy' := abs_le.mp hy
    nlinarith [sq_nonneg (Z n w-Y w),sq_nonneg (2*K-(Z n w-Y w)),sq_nonneg (2*K+(Z n w-Y w))]
  have hh := tendsto_integral_of_dominated_convergence (fun _ : Ω => 4*K^2)
    (fun n => ((hZ n).sub hY).pow 2) (integrable_const _) hdom
    (hc.mono fun w hw => by simpa using (hw.sub tendsto_const_nhds).pow 2)
  simpa only [Pi.pow_apply,Pi.sub_apply,sub_self,zero_pow (by norm_num : (2:ℕ)≠0),integral_zero] using hh

/-- The discount at the stopping time equals the discount at maturity
because the payment is zero on an early knockout. -/
theorem barrier_stopped_discount (r T ρ payoff : ℝ) (hρ : ρ≤T)
    (hz : ρ<T → payoff=0) : Real.exp (-r*ρ)*payoff=Real.exp (-r*T)*payoff := by
  rcases lt_or_eq_of_le hρ with h | h
  · simp only [hz h,mul_zero]
  · rw [h]

end Asakura.Chapter11

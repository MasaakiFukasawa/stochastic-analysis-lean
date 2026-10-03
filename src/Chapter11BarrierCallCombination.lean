import Chapter11BarrierEndpoint
import Chapter11DigitalPDE
import Chapter4GaussianPayoff

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal
namespace Asakura.Chapter11
open Asakura.Chapter4
set_option maxHeartbeats 3800000
set_option backward.isDefEq.respectTransparency false

/-- The discontinuous digital payoff is evaluated directly, rather than
using the continuous-payoff European theorem outside its assumptions. -/
theorem digital_gaussian_payoff (s b r σ θ : ℝ)
    (hs : 0<s) (hb : 0<b) (hσ : 0<σ) (hθ : 0<θ) :
    (∫ z,Real.exp (-r*θ)*(if b<s*Real.exp ((r-σ^2/2)*θ+σ*Real.sqrt θ*z) then (1:ℝ) else 0) ∂gaussianReal 0 1)=
      digitalPrice b r σ θ s := by
  let a := -bsD b (r-σ^2/2) σ s θ
  have hv : 0<σ*Real.sqrt θ := mul_pos hσ (Real.sqrt_pos.mpr hθ)
  have hb' : b=s*Real.exp ((r-σ^2/2)*θ+(σ*Real.sqrt θ)*a) := by
    have he : (r-σ^2/2)*θ+(σ*Real.sqrt θ)*a=-Real.log (s/b) := by
      dsimp only [a,bsD]
      field_simp
      ring
    rw [he,Real.exp_neg,Real.exp_log (div_pos hs hb)]
    field_simp
  have he z : b<s*Real.exp ((r-σ^2/2)*θ+σ*Real.sqrt θ*z) ↔ a<z := by
    rw [hb',mul_lt_mul_iff_right₀ hs,Real.exp_lt_exp]
    constructor <;> intro h <;> nlinarith
  simp_rw [he]
  rw [integral_const_mul]
  have hi : (fun z : ℝ => if a<z then (1:ℝ) else 0)=(Ioi a).indicator (fun _ => (1:ℝ)) := rfl
  rw [hi,integral_indicator measurableSet_Ioi,integral_const]
  simp only [smul_eq_mul,mul_one,Measure.real,Measure.restrict_apply_univ]
  have ht := normal_tail a
  change ((gaussianReal 0 1) (Ioi a)).toReal=normalCDF (-a) at ht
  rw [ht]
  simp only [a,neg_neg,digitalPrice]

/-- The bounded truncated Gaussian price is exactly the combination of
two calls and a digital price printed in the manuscript. -/
theorem barrier_gaussian_call_combination (b K r σ θ y : ℝ)
    (hb : 0<b) (hK : 0<K) (hKb : K<b) (hσ : 0<σ) (hθ : 0<θ) :
    Real.exp (-r*θ)*barrierGaussianAverage b K (r-σ^2/2) σ θ y=
      bsCall K r 0 σ (b*Real.exp y) θ-bsCall b r 0 σ (b*Real.exp y) θ-
        (b-K)*digitalPrice b r σ θ (b*Real.exp y) := by
  let S := fun z => (b*Real.exp y)*Real.exp ((r-σ^2/2)*θ+σ*Real.sqrt θ*z)
  have hs : 0<b*Real.exp y := mul_pos hb (Real.exp_pos _)
  have hSi : Integrable S (gaussianReal 0 1) := by
    simpa only [S,Real.exp_add,mul_assoc] using
      (integrable_exp_mul_gaussianReal (μ:=0) (v:=1) (σ*Real.sqrt θ)).const_mul ((b*Real.exp y)*Real.exp ((r-σ^2/2)*θ))
  have hcK : Integrable (fun z => max (S z-K) 0) (gaussianReal 0 1) := (hSi.sub (integrable_const K)).sup (integrable_const 0)
  have hcb : Integrable (fun z => max (S z-b) 0) (gaussianReal 0 1) := (hSi.sub (integrable_const b)).sup (integrable_const 0)
  have hd : Integrable (fun z => if b<S z then (1:ℝ) else 0) (gaussianReal 0 1) := by
    have hSm : Measurable S := by dsimp only [S];fun_prop
    exact (integrable_const 1).indicator (measurableSet_lt measurable_const hSm)
  have heS z : S z=b*Real.exp (y+(r-σ^2/2)*θ+σ*Real.sqrt θ*z) := by
    simp only [S,Real.exp_add]
    ring
  let a := -(y+(r-σ^2/2)*θ)/(σ*Real.sqrt θ)
  letI := nullSingletonClass_gaussianReal (μ:=0) (v:=1) (by norm_num)
  have hne : ∀ᵐ z ∂gaussianReal 0 1,z≠a := by rw [ae_iff];simp
  have hp : (fun z => if y+(r-σ^2/2)*θ+σ*Real.sqrt θ*z<0 then max (b*Real.exp (y+(r-σ^2/2)*θ+σ*Real.sqrt θ*z)-K) 0 else 0)=ᵐ[gaussianReal 0 1]
      fun z => max (S z-K) 0-max (S z-b) 0-(b-K)*(if b<S z then 1 else 0) := by
    filter_upwards [hne] with z hz
    have hSb : S z≠b := by
      intro h
      rw [heS] at h
      have he : Real.exp (y+(r-σ^2/2)*θ+σ*Real.sqrt θ*z)=1 := (mul_eq_left₀ hb.ne').mp h
      have hzero : y+(r-σ^2/2)*θ+σ*Real.sqrt θ*z=0 := by
        have hh := congrArg Real.log he
        simpa only [Real.log_exp,Real.log_one] using hh
      apply hz
      dsimp only [a]
      apply (eq_div_iff (mul_pos hσ (Real.sqrt_pos.mpr hθ)).ne').mpr
      nlinarith
    have hlt : S z<b ↔ y+(r-σ^2/2)*θ+σ*Real.sqrt θ*z<0 := by
      calc
        S z<b ↔ b*Real.exp (y+(r-σ^2/2)*θ+σ*Real.sqrt θ*z)<b*Real.exp 0 := by rw [heS];simp
        _ ↔ y+(r-σ^2/2)*θ+σ*Real.sqrt θ*z<0 := by rw [mul_lt_mul_iff_right₀ hb,Real.exp_lt_exp]
    rw [barrier_truncated_payoff (S z) K b hKb hSb]
    simp only [←heS,←hlt]
  have hc1 := bs_call_gaussian_payoff (b*Real.exp y) K r 0 σ θ hs hK hσ hθ
  have hc2 := bs_call_gaussian_payoff (b*Real.exp y) b r 0 σ θ hs hb hσ hθ
  have hd1 := digital_gaussian_payoff (b*Real.exp y) b r σ θ hs hb hσ hθ
  simp only [sub_zero,max_comm 0,integral_const_mul] at hc1 hc2
  rw [integral_const_mul] at hd1
  dsimp only [barrierGaussianAverage]
  rw [integral_congr_ae hp]
  rw [integral_sub (f:=fun z => max (S z-K) 0-max (S z-b) 0) (g:=fun z => (b-K)*(if b<S z then 1 else 0))
    (hcK.sub hcb) (hd.const_mul _),integral_sub hcK hcb,integral_const_mul]
  change Real.exp (-r*θ)*((∫ z,max (S z-K) 0 ∂gaussianReal 0 1)-(∫ z,max (S z-b) 0 ∂gaussianReal 0 1)-(b-K)*(∫ z,if b<S z then (1:ℝ) else 0 ∂gaussianReal 0 1))=_
  rw [show (fun z => max (S z-K) 0)=(fun z => max 0 (S z-K)) by funext z;exact max_comm _ _,
    show (fun z => max (S z-b) 0)=(fun z => max 0 (S z-b)) by funext z;exact max_comm _ _]
  dsimp only [S]
  linear_combination hc1-hc2-(b-K)*hd1

end Asakura.Chapter11

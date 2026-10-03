import Chapter12GaussianMixtureFourier
import EndToEndDensityL1
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
namespace Asakura.EndToEnd
open Asakura.Chapter12
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false

/-- At each positive Gaussian variance, convergence of characteristic
 functions gives pointwise convergence of the actual convolution densities. -/
theorem gaussian_smoothing_pointwise {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (μ : ℕ → Measure E) (ν : Measure E)
    [∀ n,IsProbabilityMeasure (μ n)] [IsProbabilityMeasure ν]
    (hlim : ∀ ξ,Tendsto (fun n => charFun (μ n) ξ) atTop (𝓝 (charFun ν ξ)))
    (b : ℝ) (hb : 0 < b) (x : E) :
    Tendsto (fun n => ∫ y,normalizedGaussianKernel (1/(4*b)) (x-y) ∂μ n) atTop
      (𝓝 (∫ y,normalizedGaussianKernel (1/(4*b)) (x-y) ∂ν)) := by
  let k := fun ξ : E => Real.exp (-b*‖ξ‖^2)
  have hk : Integrable k := by
    have hh := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
      (V:=E) (b:=(b:ℂ)) (show 0 < (b:ℂ).re from hb) 0 (0:E)).re
    change Integrable (fun ξ : E => (Complex.exp (-(b:ℂ)*(‖ξ‖:ℂ)^2+(0:ℂ)*(inner ℝ (0:E) ξ:ℂ))).re) at hh
    simpa only [k,zero_mul,add_zero,← Complex.ofReal_pow,← Complex.ofReal_mul,
      ← Complex.ofReal_neg,← Complex.ofReal_exp,Complex.ofReal_re] using hh
  let phase := fun ξ : E => Complex.exp (-Complex.I*(inner ℝ ξ x:ℂ))
  have hphase ξ : ‖phase ξ‖ = 1 := by simp [phase,Complex.norm_exp]
  have hm n : AEStronglyMeasurable (fun ξ => phase ξ*charFun (μ n) ξ*(k ξ:ℂ)) volume := by
    exact ((show Continuous phase by fun_prop).mul continuous_charFun |>.mul
      (show Continuous (fun ξ => (k ξ:ℂ)) by fun_prop)).aestronglyMeasurable
  have hbound n ξ : ‖phase ξ*charFun (μ n) ξ*(k ξ:ℂ)‖ ≤ k ξ := by
    rw [norm_mul,norm_mul,hphase,one_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    exact (mul_le_mul_of_nonneg_right (norm_charFun_le_one ξ) (Real.exp_pos _).le).trans_eq (one_mul _)
  have ht := tendsto_integral_of_dominated_convergence k hm hk
    (fun n => .of_forall (hbound n))
    (.of_forall (fun ξ => ((hlim ξ).const_mul (phase ξ)).mul_const (k ξ:ℂ)))
  have hfourier (ρ : Measure E) [IsProbabilityMeasure ρ] :
      ((∫ y,normalizedGaussianKernel (1/(4*b)) (x-y) ∂ρ : ℝ):ℂ) =
      ((2*Real.pi)^Module.finrank ℝ E:ℂ)⁻¹ * ∫ ξ,phase ξ*charFun ρ ξ*(k ξ:ℂ) := by
    simpa only [phase,k,charFun,real_inner_comm,mul_comm Complex.I]
      using gaussian_mixture_fourier ρ b hb x
  have ht' := ht.const_mul (((2*Real.pi)^Module.finrank ℝ E:ℂ)⁻¹)
  simp only [← hfourier] at ht'
  exact Complex.continuous_re.continuousAt.tendsto.comp ht'

#print axioms gaussian_smoothing_pointwise
end Asakura.EndToEnd

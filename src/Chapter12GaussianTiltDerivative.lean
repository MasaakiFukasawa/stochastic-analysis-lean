import Chapter12GaussianAbsoluteExponential
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Deriv.Pow

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

theorem gaussian_tilt_kernel_derivative (f z v t : ℝ) :
    HasDerivAt (fun s => f*Real.exp (s*z-s^2*v/2))
      (f*Real.exp (t*z-t^2*v/2)*(z-t*v)) t := by
  have hh := (((hasDerivAt_id t).mul_const z).sub
    ((((hasDerivAt_id t).pow 2).mul_const v).div_const 2)).exp.const_mul f
  convert hh using 1 <;> (try funext s) <;> (try dsimp) <;> ring

theorem gaussian_tilt_kernel_bound (f z v t R : ℝ) (hv : 0≤v)
    (hR : 0≤R) (ht : |t|≤R) :
    |f*Real.exp (t*z-t^2*v/2)*(z-t*v)|≤
      (1+R*v)*(|f| *Real.exp (R*|z|)*(1+|z|)) := by
  have htz : |t*z|≤R*|z| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right ht (abs_nonneg z)
  have he : t*z-t^2*v/2≤R*|z| := by
    have hh := (le_abs_self (t*z)).trans htz
    nlinarith [mul_nonneg (sq_nonneg t) hv]
  have htv : |t*v|≤R*v := by
    rw [abs_mul,abs_of_nonneg hv]
    exact mul_le_mul_of_nonneg_right ht hv
  have hz : |z-t*v|≤(1+R*v)*(1+|z|) := by
    have hh : |z-t*v|≤|z|+R*v := (abs_sub z (t*v)).trans (add_le_add le_rfl htv)
    nlinarith [abs_nonneg z,mul_nonneg hR hv,mul_nonneg (mul_nonneg hR hv) (abs_nonneg z)]
  rw [abs_mul,abs_mul,abs_of_pos (Real.exp_pos _)]
  calc
    _≤|f| *Real.exp (R*|z|)*((1+R*v)*(1+|z|)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (abs_nonneg f)) hz
        (abs_nonneg _) (by positivity)
    _=_ := by ring

/-- Differentiation under a Gaussian likelihood ratio is valid for every
L2 payoff. This is the measurable-payoff extension needed by basket Greeks. -/
theorem gaussian_tilt_expectation_derivative {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Z f : Ω → ℝ) (v : ℝ≥0)
    (hZ : HasLaw Z (gaussianReal 0 v) P) (hf : MemLp f 2 P) (t : ℝ) :
    HasDerivAt (fun s => ∫ w,f w*Real.exp (s*Z w-s^2*v/2) ∂P)
      (∫ w,f w*Real.exp (t*Z w-t^2*v/2)*(Z w-t*v) ∂P) t := by
  let R : ℝ := |t|+1
  have hR : 0≤R := by dsimp [R]; positivity
  have hs : Ioo (t-1) (t+1)∈𝓝 t := Ioo_mem_nhds (by linarith) (by linarith)
  have htR : ∀ s∈Ioo (t-1) (t+1),|s|≤R := by
    intro s hs
    apply abs_le.mpr
    constructor <;> dsimp [R] <;> linarith [le_abs_self t,neg_abs_le t,hs.1,hs.2]
  have hiExp : MemLp (fun w => Real.exp (t*Z w-t^2*v/2)) 2 P := by
    have hh := (gaussian_exponential_memLp P Z 0 v hZ t 2 (by norm_num)).const_mul
      (Real.exp (-t^2*v/2))
    convert hh using 1
    funext w
    rw [← Real.exp_add]
    congr 1
    ring
  have hi : Integrable (fun w => f w*Real.exp (t*Z w-t^2*v/2)) P := hf.integrable_mul hiExp
  have hm (s : ℝ) : AEStronglyMeasurable (fun w => f w*Real.exp (s*Z w-s^2*v/2)) P :=
    hf.aestronglyMeasurable.mul (Real.measurable_exp.comp_aemeasurable ((hZ.aemeasurable.const_mul s).sub_const _)).aestronglyMeasurable
  have hmd : AEStronglyMeasurable (fun w => f w*Real.exp (t*Z w-t^2*v/2)*(Z w-t*v)) P :=
    (hm t).mul (hZ.aemeasurable.sub_const _).aestronglyMeasurable
  have hb := (gaussian_payoff_score_envelope_integrable P Z f 0 v hZ hf R 1).const_mul (1+R*v)
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := P) hs
    (Eventually.of_forall hm) hi hmd _ hb _).2
  · filter_upwards [] with w s hs
    simpa only [Real.norm_eq_abs,pow_one] using
      gaussian_tilt_kernel_bound (f w) (Z w) v s R v.property hR (htR s hs)
  · exact ae_of_all _ (fun w s _ => gaussian_tilt_kernel_derivative (f w) (Z w) v s)

end Asakura.Chapter12

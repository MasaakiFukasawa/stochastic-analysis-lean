import Chapter8ConvexCoercivity
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

open MeasureTheory
open scoped RealInnerProductSpace
namespace Asakura.Chapter8
set_option maxHeartbeats 500000

/-- A Gaussian majorant is integrable for Lebesgue measure in every finite dimension. -/
theorem integrable_gaussian_norm {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (a : ℝ) (ha : 0 < a) : Integrable (fun x : E => Real.exp (-a*‖x‖^2)) := by
  have hh := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := E) (b := (a:ℂ))
    (by simpa using ha) 0 0).norm
  convert hh using 1
  funext x
  simp [Complex.norm_exp,pow_two]

/-- A second moment can be absorbed into a Gaussian of half the precision. -/
theorem integrable_quadratic_gaussian {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (a : ℝ) (ha : 0 < a) : Integrable (fun x : E => (1+‖x‖^2)*Real.exp (-a*‖x‖^2)) := by
  apply ((integrable_gaussian_norm (E := E) (a/2) (by positivity)).const_mul (1+2/a)).mono'
    (by fun_prop)
  apply ae_of_all _
  intro x
  rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  have he := Real.add_one_le_exp (a/2*‖x‖^2)
  have h1 : 1 ≤ Real.exp (a/2*‖x‖^2) := Real.one_le_exp_iff.mpr (by positivity)
  have hq : ‖x‖^2 ≤ (2/a)*Real.exp (a/2*‖x‖^2) := by
    have hmul : a*(2/a)=2 := mul_div_cancel₀ 2 ha.ne'
    nlinarith
  have hb : 1+‖x‖^2 ≤ (1+2/a)*Real.exp (a/2*‖x‖^2) := by nlinarith
  have hh := mul_le_mul_of_nonneg_right hb (Real.exp_pos (-a*‖x‖^2)).le
  rw [mul_assoc,← Real.exp_add] at hh
  convert hh using 1 <;> congr 2 <;> ring

/-- A quadratic lower bound yields both the normalising integral and the
second Gibbs moment, without a convexity assumption on the potential. -/
theorem gibbs_second_moment_integrable {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (U : E → ℝ) (hU : Continuous U) (a b β : ℝ) (ha : 0 < a) (hβ : 0 < β)
    (hlower : ∀ x, a*‖x‖^2+b ≤ U x) :
    Integrable (fun x : E => (1+‖x‖^2)*Real.exp (-β*U x)) := by
  apply ((integrable_quadratic_gaussian (E := E) (β*a) (mul_pos hβ ha)).const_mul
    (Real.exp (-β*b))).mono' (by fun_prop)
  apply ae_of_all _
  intro x
  rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  calc
    (1+‖x‖^2)*Real.exp (-β*U x) ≤ (1+‖x‖^2)*Real.exp (-β*(a*‖x‖^2+b)) := by
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr _) (by positivity)
      nlinarith [hlower x]
    _ = Real.exp (-β*b)*((1+‖x‖^2)*Real.exp (-(β*a)*‖x‖^2)) := by
      rw [show -β*(a*‖x‖^2+b) = -β*b+(-(β*a)*‖x‖^2) by ring,Real.exp_add]
      ring

/-- The hypotheses used in the uniformly convex part of the chapter imply
both a finite positive partition function and a finite second moment. -/
theorem strongly_convex_gibbs_integrability {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (U : E → ℝ) (g : E → E) (H : E → E →L[ℝ] E) (κ β : ℝ)
    (hκ : 0 < κ) (hβ : 0 < β)
    (hU : ∀ x, HasFDerivAt U (innerSL ℝ (g x)) x)
    (hg : ∀ x, HasFDerivAt g (H x) x)
    (hH : ∀ x v, κ*‖v‖^2 ≤ ⟪v,H x v⟫) :
    Integrable (fun x : E => (1+‖x‖^2)*Real.exp (-β*U x)) ∧
    Integrable (fun x : E => Real.exp (-β*U x)) ∧
    0 < ∫ x : E, Real.exp (-β*U x) := by
  have hc : Continuous U := continuous_iff_continuousAt.mpr (fun x => (hU x).continuousAt)
  have hi := gibbs_second_moment_integrable U hc (κ/4) (U 0-‖g 0‖^2/κ) β
    (by positivity) hβ (fun x => by
      have hh := strongly_convex_coercive_bound U g H κ hκ hU hg hH x
      linarith)
  have h0 : Integrable (fun x : E => Real.exp (-β*U x)) := by
    apply hi.mono' (by fun_prop)
    apply ae_of_all _
    intro x
    rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    nlinarith [sq_nonneg ‖x‖,Real.exp_pos (-β*U x)]
  exact ⟨hi,h0,integral_exp_pos h0⟩

/-- The explicitly nonconvex cosine example still has Gaussian tails. -/
theorem cosine_gibbs_second_moment (c β : ℝ) (hβ : 0 < β) :
    Integrable (fun x : ℝ => (1+‖x‖^2)*Real.exp (-β*(x^2/2+c*Real.cos x))) := by
  apply gibbs_second_moment_integrable (fun x : ℝ => x^2/2+c*Real.cos x)
    (by fun_prop) (1/2) (-|c|) β (by norm_num) hβ
  intro x
  have hh : |c*Real.cos x| ≤ |c| := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one x) (abs_nonneg c)).trans_eq (mul_one _)
  have hl := neg_le_of_abs_le hh
  simp only [Real.norm_eq_abs,sq_abs]
  linarith

end Asakura.Chapter8

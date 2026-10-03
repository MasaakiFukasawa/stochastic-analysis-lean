import Chapter4VectorInitialStability
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal
namespace Asakura.Chapter4
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

lemma first_norm_moment_le_sqrt_second
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    (P : Measure Ω) [IsProbabilityMeasure P] (Z : Ω → E) (hi : MemLp Z 2 P) :
    (∫ w,‖Z w‖ ∂P)≤Real.sqrt (∫ w,‖Z w‖^2 ∂P) := by
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg (μ:=P) Real.HolderConjugate.two_two
    (f:=fun w => ‖Z w‖) (g:=fun _ => (1:ℝ))
    (Filter.Eventually.of_forall (fun w => norm_nonneg _))
    (Filter.Eventually.of_forall (fun _ => zero_le_one)) (by simpa using hi.norm) (memLp_const 1)
  simpa only [mul_one,Real.rpow_two,one_pow,integral_const,probReal_univ,smul_eq_mul,one_mul,
    Real.one_rpow,Real.sqrt_eq_rpow] using hh

lemma lipschitz_expectation_difference_le
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P] (X Y : Ω → E)
    (hXm : Measurable X) (hYm : Measurable Y) (hXi : MemLp X 2 P) (hYi : MemLp Y 2 P)
    (f : E → ℝ) (L : ℝ≥0) (hL : LipschitzWith L f) (B : ℝ) (hb : ∀ x,‖f x‖≤B) :
    ‖(∫ w,f (X w) ∂P)-(∫ w,f (Y w) ∂P)‖≤(L:ℝ)*Real.sqrt (∫ w,‖X w-Y w‖^2 ∂P) := by
  have hfiX : Integrable (fun w => f (X w)) P := (integrable_const B).mono'
    (hL.continuous.measurable.comp hXm).aestronglyMeasurable (Filter.Eventually.of_forall (fun w => hb _))
  have hfiY : Integrable (fun w => f (Y w)) P := (integrable_const B).mono'
    (hL.continuous.measurable.comp hYm).aestronglyMeasurable (Filter.Eventually.of_forall (fun w => hb _))
  have hnorm := (hXi.sub hYi).norm.integrable (by norm_num : (1:ℝ≥0∞)≤2)
  rw [← integral_sub hfiX hfiY]
  calc
    _ ≤ ∫ w,‖f (X w)-f (Y w)‖ ∂P := norm_integral_le_integral_norm _
    _ ≤ ∫ w,(L:ℝ)*‖X w-Y w‖ ∂P := integral_mono (hfiX.sub hfiY).norm (hnorm.const_mul _)
      (fun w => by simpa only [dist_eq_norm] using hL.dist_le_mul (X w) (Y w))
    _ = (L:ℝ)*(∫ w,‖X w-Y w‖ ∂P) := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (first_norm_moment_le_sqrt_second P (fun w => X w-Y w) (hXi.sub hYi)) L.coe_nonneg

/-- Stability of solutions makes the transition operator preserve bounded
Lipschitz functions, the continuity used for simple-initial-value limits. -/
theorem transition_operator_lipschitz_of_square_stability
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : E → Ω → E)
    (hXm : ∀ x,Measurable (X x)) (hXi : ∀ x,MemLp (X x) 2 P)
    (C : ℝ) (hC : 0≤C) (hs : ∀ x y,(∫ w,‖X x w-X y w‖^2 ∂P)≤C*‖x-y‖^2)
    (f : E → ℝ) (L : ℝ≥0) (hL : LipschitzWith L f) (B : ℝ) (hb : ∀ x,‖f x‖≤B) :
    LipschitzWith ⟨(L:ℝ)*Real.sqrt C,by positivity⟩ (fun x => ∫ w,f (X x w) ∂P) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm,dist_eq_norm]
  have hh := lipschitz_expectation_difference_le P (X x) (X y) (hXm x) (hXm y) (hXi x) (hXi y) f L hL B hb
  have hsqrt := Real.sqrt_le_sqrt (hs x y)
  rw [Real.sqrt_mul hC,Real.sqrt_sq (norm_nonneg _)] at hsqrt
  change _≤((L:ℝ)*Real.sqrt C)*‖x-y‖
  exact hh.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hsqrt L.coe_nonneg)

end Asakura.Chapter4

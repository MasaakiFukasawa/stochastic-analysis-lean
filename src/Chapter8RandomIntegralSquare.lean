import Chapter2CumulativeBound
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory Set
open scoped ENNReal
namespace Asakura.Chapter8
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

theorem finite_measure_integral_square {A E : Type*} [MeasurableSpace A]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (μ : Measure A) [IsFiniteMeasure μ]
    (f : A → E) (hf : MemLp f 2 μ) :
    ‖∫ x,f x ∂μ‖^2≤μ.real univ*(∫ x,‖f x‖^2 ∂μ) := by
  have hh := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
    (by simpa using hf.norm : MemLp (fun x => ‖f x‖) (ENNReal.ofReal 2) μ)
    (memLp_const (μ := μ) (1:ℝ) : MemLp (fun _ : A => (1:ℝ)) (ENNReal.ofReal 2) μ)
  have hcs : (∫ x,‖f x‖ ∂μ)≤Real.sqrt (∫ x,‖f x‖^2 ∂μ)*Real.sqrt (μ.real univ) := by
    simpa only [Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _),abs_one,mul_one,Real.rpow_two,
      one_pow,integral_const,smul_eq_mul,←Real.sqrt_eq_rpow] using hh
  have hn := (norm_integral_le_integral_norm f).trans hcs
  have hp := pow_le_pow_left₀ (norm_nonneg _) hn 2
  rw [mul_pow,Real.sq_sqrt (integral_nonneg (fun _ => sq_nonneg _)),Real.sq_sqrt (show 0≤μ.real univ from ENNReal.toReal_nonneg),mul_comm] at hp
  exact hp

/-- Cauchy--Schwarz and Fubini for the actual random drift integral.
A finite weighted time measure is allowed, giving the square of its mass. -/
theorem random_integral_square_estimate {Ω A E : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (P : Measure Ω) [IsProbabilityMeasure P] (μ : Measure A) [IsFiniteMeasure μ]
    (H : Ω × A → E) (hH : Measurable H) (h2 : MemLp H 2 (P.prod μ))
    :
    MemLp (fun w => ∫ t,H (w,t) ∂μ) 2 P ∧
      (∫ w,‖∫ t,H (w,t) ∂μ‖^2 ∂P)≤μ.real univ*(∫ t,(∫ w,‖H (w,t)‖^2 ∂P) ∂μ) := by
  have hi := h2.integrable_norm_pow (by norm_num : (2:ℕ)≠0)
  have hs : ∀ᵐ w ∂P,MemLp (fun t => H (w,t)) 2 μ := by
    filter_upwards [hi.prod_right_ae] with w hw
    exact (memLp_two_iff_integrable_sq_norm (hH.comp measurable_prodMk_left).aestronglyMeasurable).mpr hw
  have hm : Measurable (fun w => ∫ t,H (w,t) ∂μ) :=
    (show StronglyMeasurable (Function.uncurry (fun w t => H (w,t))) from hH.stronglyMeasurable).integral_prod_right.measurable
  have hd : Integrable (fun w => μ.real univ*(∫ t,‖H (w,t)‖^2 ∂μ)) P := hi.integral_prod_left.const_mul _
  have he : ∀ᵐ w ∂P,‖∫ t,H (w,t) ∂μ‖^2≤μ.real univ*(∫ t,‖H (w,t)‖^2 ∂μ) :=
    hs.mono (fun w hw => finite_measure_integral_square μ _ hw)
  have hsq : Integrable (fun w => ‖∫ t,H (w,t) ∂μ‖^2) P :=
    hd.mono' (hm.norm.pow_const 2).aestronglyMeasurable (he.mono (fun w hw => by simpa only [Real.norm_eq_abs,abs_sq] using hw))
  refine ⟨(memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr hsq,?_⟩
  calc
    _ ≤ ∫ w,μ.real univ*(∫ t,‖H (w,t)‖^2 ∂μ) ∂P := integral_mono_ae hsq hd he
    _ = μ.real univ*(∫ t,(∫ w,‖H (w,t)‖^2 ∂P) ∂μ) := by
      rw [integral_const_mul,integral_integral_swap hi]

/-- Cauchy--Schwarz and Fubini for the actual random drift integral.
A finite weighted time measure is allowed, giving the square of its mass. -/
theorem random_integral_square_bound {Ω A E : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (P : Measure Ω) [IsProbabilityMeasure P] (μ : Measure A) [IsFiniteMeasure μ]
    (H : Ω × A → E) (hH : Measurable H) (h2 : MemLp H 2 (P.prod μ))
    (C : ℝ) (hb : ∀ᵐ t ∂μ,(∫ w,‖H (w,t)‖^2 ∂P)≤C) :
    MemLp (fun w => ∫ t,H (w,t) ∂μ) 2 P ∧
      (∫ w,‖∫ t,H (w,t) ∂μ‖^2 ∂P)≤(μ.real univ)^2*C := by
  have hi := h2.integrable_norm_pow (by norm_num : (2:ℕ)≠0)
  have hs : ∀ᵐ w ∂P,MemLp (fun t => H (w,t)) 2 μ := by
    filter_upwards [hi.prod_right_ae] with w hw
    exact (memLp_two_iff_integrable_sq_norm (hH.comp measurable_prodMk_left).aestronglyMeasurable).mpr hw
  have hm : Measurable (fun w => ∫ t,H (w,t) ∂μ) :=
    (show StronglyMeasurable (Function.uncurry (fun w t => H (w,t))) from hH.stronglyMeasurable).integral_prod_right.measurable
  have hd : Integrable (fun w => μ.real univ*(∫ t,‖H (w,t)‖^2 ∂μ)) P := hi.integral_prod_left.const_mul _
  have he : ∀ᵐ w ∂P,‖∫ t,H (w,t) ∂μ‖^2≤μ.real univ*(∫ t,‖H (w,t)‖^2 ∂μ) :=
    hs.mono (fun w hw => finite_measure_integral_square μ _ hw)
  have hsq : Integrable (fun w => ‖∫ t,H (w,t) ∂μ‖^2) P :=
    hd.mono' (hm.norm.pow_const 2).aestronglyMeasurable (he.mono (fun w hw => by simpa only [Real.norm_eq_abs,abs_sq] using hw))
  refine ⟨(memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr hsq,?_⟩
  calc
    _ ≤ ∫ w,μ.real univ*(∫ t,‖H (w,t)‖^2 ∂μ) ∂P := integral_mono_ae hsq hd he
    _ = μ.real univ*(∫ t,(∫ w,‖H (w,t)‖^2 ∂P) ∂μ) := by
      rw [integral_const_mul,integral_integral_swap hi]
    _ ≤ μ.real univ*(∫ _t,C ∂μ) := mul_le_mul_of_nonneg_left
      (integral_mono_ae hi.integral_prod_right (integrable_const C) hb) ENNReal.toReal_nonneg
    _ = _ := by rw [integral_const,smul_eq_mul]; ring
end Asakura.Chapter8

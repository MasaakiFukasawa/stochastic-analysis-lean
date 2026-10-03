import Chapter4GaussianPayoff
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Function.L2Space

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
namespace Asakura.Chapter11
set_option maxHeartbeats 1800000

/-- Every real moment of a lognormal variable is finite. -/
theorem lognormal_real_moment_integrable (s a b q : ℝ) (hs : 0<s) :
    Integrable (fun z => (s*Real.exp (a+b*z))^q) (gaussianReal 0 1) := by
  have he : (fun z => (s*Real.exp (a+b*z))^q)=
      (fun z => (s^q*Real.exp (a*q))*Real.exp ((b*q)*z)) := by
    funext z
    rw [Real.mul_rpow hs.le (Real.exp_pos _).le,←Real.exp_mul,show (a+b*z)*q=a*q+(b*q)*z by ring,
      Real.exp_add]
    ring
  rw [he]
  exact (integrable_exp_mul_gaussianReal (μ:=0) (v:=1) (b*q)).const_mul _

/-- A continuous positive-price payoff of real polynomial growth is in L2.
The subtype keeps continuity restricted to (0,infinity), as in the book. -/
theorem polynomial_payoff_memLp_two {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q] (S : Ω → Ioi (0:ℝ)) (hS : Measurable S)
    (h : Ioi (0:ℝ) → ℝ) (hh : Continuous h) (C m : ℝ)
    (hb : ∀ x,‖h x‖≤C*(1+(x.val)^m))
    (hi : Integrable (fun w => ((S w).val)^(2*m)) Q) : MemLp (fun w => h (S w)) 2 Q := by
  have hm : Measurable (fun w => ((S w).val)^m) := (measurable_subtype_coe.comp hS).pow_const m
  have hpow : MemLp (fun w => ((S w).val)^m) 2 Q := by
    apply (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr
    convert hi using 1
    funext w
    rw [show 2*m=m*(2:ℕ) by norm_num;ring,Real.rpow_mul_natCast (S w).property.le]
  have hdom : MemLp (fun w => C*(1+((S w).val)^m)) 2 Q :=
    ((memLp_const (1:ℝ)).add hpow).const_mul C
  exact hdom.mono' (hh.measurable.comp hS).aestronglyMeasurable (ae_of_all _ fun w => hb (S w))

end Asakura.Chapter11

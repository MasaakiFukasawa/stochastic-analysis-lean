import Chapter3IncreasingAdaptedVariation
import Chapter3C1WeightedProduct
import Chapter4ClockRegularity

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 1800000

lemma exponential_adapted_variation
    {Ω : Type*} {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F)
    (A : ClosedTime T → Ω → ℝ)
    (ha : ∀ t,t<⊤ → Measurable[F t] (A t))
    (hm : ∀ w,MonotoneOn (fun t => A t w) (Iio ⊤))
    (hc : ∀ w t,t<⊤ → ContinuousAt (fun s => A s w) t) (a : ℝ) :
    AdaptedLocalVariationWitness F (fun t w => Real.exp (a*A t w)) := by
  have hma t ht : Measurable[F t] (fun w => Real.exp (a*A t w)) := (measurable_const.mul (ha t ht)).exp
  have hca w t ht : ContinuousAt (fun s => Real.exp (a*A s w)) t := Real.continuous_exp.continuousAt.comp (continuousAt_const.mul (hc w t ht))
  by_cases h : 0≤a
  · apply continuous_increasing_adapted_variation hT F hF _ hma _ hca
    intro w s hs t ht hst
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hm w hs ht hst) h)
  · have hn : AdaptedLocalVariationWitness F (fun t w => -Real.exp (a*A t w)) := by
      apply continuous_increasing_adapted_variation hT F hF _ (fun t ht => (hma t ht).neg) _ (fun w t ht => (hca w t ht).neg)
      intro w s hs t ht hst
      exact neg_le_neg (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left (hm w hs ht hst) (le_of_not_ge h)))
    simpa only [neg_one_mul,neg_neg] using hn.smul (-1)

lemma exponential_weight_integral (a d : ℝ) :
    Real.exp (a*d)=1+a*(∫ r in 0..d,Real.exp (a*r)) := by
  have hder r : HasDerivAt (fun s => Real.exp (a*s)) (a*Real.exp (a*r)) r := by
    convert ((hasDerivAt_id r).const_mul a).exp using 1 <;> simp only [id_eq] <;> ring
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r (_ : r∈uIcc 0 d) => hder r)
    ((by fun_prop : Continuous (fun r => a*Real.exp (a*r))).intervalIntegrable 0 d)
  rw [intervalIntegral.integral_const_mul] at he
  simp only [mul_zero,Real.exp_zero] at he
  linarith only [he]

end Asakura.Chapter4

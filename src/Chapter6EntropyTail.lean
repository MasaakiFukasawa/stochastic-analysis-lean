import Chapter6LikelihoodPushforward
import Mathlib.Analysis.SpecialFunctions.Log.Monotone

open MeasureTheory Set Filter
open scoped ENNReal
namespace Asakura.Chapter6
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

lemma entropy_pointwise_lower (x : ℝ) (hx : 0 ≤ x) :
    -Real.exp (-1) ≤ x*Real.log x := by
  by_cases h : x ≤ Real.exp (-1)
  · have hh := Real.mul_log_strictAntiOn.antitoneOn ⟨hx,h⟩ ⟨(Real.exp_pos _).le,le_rfl⟩ h
    simpa only [Real.log_exp,mul_neg,mul_one] using hh
  · have hh : Real.exp (-1)*Real.log (Real.exp (-1)) ≤ x*Real.log x := by
      apply Real.mul_log_strictMonoOn.monotoneOn
      · exact (show Real.exp (-1) ≤ Real.exp (-1) from le_rfl)
      · exact le_of_not_ge h
      · exact le_of_not_ge h
    simpa only [Real.log_exp,mul_neg,mul_one] using hh

/-- The entropy estimate in the linear-growth density proof gives the
explicit uniform tail bound used before taking the localization limit. -/
theorem entropy_density_tail_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (D : Ω → ℝ) (hm : Measurable D) (hi : Integrable D P)
    (hp : ∀ᵐ w ∂P,0 ≤ D w)
    (hei : Integrable (fun w => D w*Real.log (D w)) P)
    (C : ℝ) (hC : (∫ w,D w*Real.log (D w) ∂P) ≤ C)
    (R : ℝ) (hR : 1 < R) :
    (∫ w in {w | R < D w},D w ∂P) ≤ (C+Real.exp (-1))/Real.log R := by
  have hS : MeasurableSet {w | R < D w} := measurableSet_lt measurable_const hm
  have htail := hi.indicator hS
  have hh : ∀ᵐ w ∂P,Real.log R*({w | R < D w}.indicator D w) ≤ D w*Real.log (D w)+Real.exp (-1) := by
    filter_upwards [hp] with w hw
    by_cases hs : R < D w
    · simp only [Set.indicator,Set.mem_setOf_eq,hs,ite_true]
      have hl := Real.log_le_log (by linarith : 0 < R) hs.le
      have hmul := mul_le_mul_of_nonneg_left hl hw
      nlinarith [Real.exp_pos (-1)]
    · simp only [Set.indicator,Set.mem_setOf_eq,hs,ite_false,mul_zero]
      linarith [entropy_pointwise_lower (D w) hw]
  have he := integral_mono_ae (htail.const_mul (Real.log R)) (hei.add (integrable_const (Real.exp (-1)))) hh
  simp only [Pi.add_apply] at he
  rw [integral_const_mul,integral_indicator hS,integral_add hei (integrable_const (Real.exp (-1)))] at he
  simp only [integral_const,Measure.real,measure_univ,ENNReal.toReal_one,one_smul] at he
  apply (le_div_iff₀ (Real.log_pos hR)).mpr
  nlinarith

end Asakura.Chapter6

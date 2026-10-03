import Chapter6NovikovHolder

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.Chapter6
set_option maxHeartbeats 2000000

/-- Holder's inequality at the critical Novikov exponent, applied first to
the exponential with its martingale term multiplied by 0 < l < 1. -/
theorem novikov_endpoint_holder
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Z C : Ω → ℝ) (hZ : Measurable Z) (hC : Measurable C)
    (hn : ∀ᵐ w ∂P,0 ≤ C w) (l : ℝ) (hl : 0 < l) (hl1 : l < 1) :
    (∫⁻ w,ENNReal.ofReal (Real.exp (l*Z w-l^2*C w/2)) ∂P) ≤
      (∫⁻ w,ENNReal.ofReal (Real.exp (Z w-C w/2)) ∂P)^l *
      (∫⁻ w,ENNReal.ofReal (Real.exp (C w/2)) ∂P)^(1-l) := by
  let U := fun w => ENNReal.ofReal (Real.exp (Z w-C w/2))
  let V := fun w => ENNReal.ofReal (Real.exp (l*C w/2))
  have hu : Measurable U := by fun_prop
  have hv : Measurable V := by fun_prop
  have hc : (1/l).HolderConjugate (1/(1-l)) := by
    apply Real.holderConjugate_iff.mpr
    refine ⟨(one_lt_div hl).mpr hl1,?_⟩
    field_simp
    <;> ring
  have hh := ENNReal.lintegral_mul_le_Lp_mul_Lq P hc
    (hu.pow_const l).aemeasurable (hv.pow_const (1-l)).aemeasurable
  have he w : ENNReal.ofReal (Real.exp (l*Z w-l^2*C w/2)) = U w^l*V w^(1-l) := by
    dsimp [U,V]
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le hl.le,
      ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le (sub_nonneg.mpr hl1.le),
      ← ENNReal.ofReal_mul (by positivity),← Real.exp_mul,← Real.exp_mul,← Real.exp_add]
    congr 2
    ring
  have hu' w : (U w^l)^(1/l) = U w := by
    rw [← ENNReal.rpow_mul,mul_one_div_cancel hl.ne',ENNReal.rpow_one]
  have hv' w : (V w^(1-l))^(1/(1-l)) = V w := by
    rw [← ENNReal.rpow_mul,mul_one_div_cancel (sub_pos.mpr hl1).ne',ENNReal.rpow_one]
  simp_rw [hu',hv'] at hh
  simp only [one_div_one_div] at hh
  simp_rw [he]
  apply hh.trans
  apply mul_le_mul' le_rfl
  apply ENNReal.rpow_le_rpow _ (sub_nonneg.mpr hl1.le)
  apply lintegral_mono_ae
  filter_upwards [hn] with w hw
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  exact div_le_div_of_nonneg_right (mul_le_of_le_one_left hw hl1.le) (by norm_num)

end Asakura.Chapter6

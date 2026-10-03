import Chapter6NovikovParameters
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

open MeasureTheory Set Filter
open scoped ENNReal
namespace Asakura.Chapter6
set_option maxHeartbeats 1500000

/-- The Holder estimate in Novikov's proof, with the two exponential
factors and their conjugate powers calculated explicitly. -/
theorem novikov_holder_bound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Z C : Ω → ℝ) (hZ : Measurable Z) (hC : Measurable C)
    (α p γ : ℝ) (ha : 1 < α)
    (hg : γ = p*((α*p-1)/(α-1))*(α/2))
    (hm : (∫⁻ w,ENNReal.ofReal (Real.exp (α*p*Z w-(α*p)^2*C w/2)) ∂P) ≤ 1) :
    (∫⁻ w,ENNReal.ofReal (Real.exp (p*(Z w-C w/2))) ∂P) ≤
      (∫⁻ w,ENNReal.ofReal (Real.exp (γ*C w)) ∂P)^((α-1)/α) := by
  have ha0 : 0 < α := by linarith
  have ha1 : 0 < α-1 := by linarith
  let q := α/(α-1)
  have hq : 0 < q := div_pos ha0 ha1
  have hpq : α.HolderConjugate q := by
    apply Real.holderConjugate_iff.mpr
    refine ⟨ha,?_⟩
    dsimp [q]
    field_simp
    ring
  let U := fun w => ENNReal.ofReal (Real.exp (α*p*Z w-(α*p)^2*C w/2))
  let V := fun w => ENNReal.ofReal (Real.exp (γ*C w))
  have hu : Measurable U := by fun_prop
  have hv : Measurable V := by fun_prop
  have hf (w) : ENNReal.ofReal (Real.exp (p*(Z w-C w/2))) = U w^(1/α)*V w^(1/q) := by
    dsimp [U,V,q]
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le (by positivity),
      ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [← Real.exp_mul,← Real.exp_mul,← Real.exp_add]
    congr 1
    have hh := novikov_exponent_split α p (Z w) (C w) (ne_of_gt ha0) (ne_of_gt ha) γ hg
    convert hh using 1 <;> field_simp <;> ring
  have hh := ENNReal.lintegral_mul_le_Lp_mul_Lq P hpq
    (hu.pow_const (1/α)).aemeasurable (hv.pow_const (1/q)).aemeasurable
  have hpow (w) : (U w^(1/α))^α = U w := by
    rw [← ENNReal.rpow_mul,one_div_mul_cancel (ne_of_gt ha0),ENNReal.rpow_one]
  have hpow' (w) : (V w^(1/q))^q = V w := by
    rw [← ENNReal.rpow_mul,one_div_mul_cancel (ne_of_gt hq),ENNReal.rpow_one]
  simp_rw [hpow,hpow'] at hh
  simp_rw [hf]
  have hb : (∫⁻ w,U w ∂P)^(1/α) ≤ 1 := by
    simpa using ENNReal.rpow_le_rpow hm (by positivity : 0 ≤ 1/α)
  have hqi : 1/q = (α-1)/α := by dsimp [q]; field_simp
  exact hh.trans (by simpa [hqi] using mul_le_mul_left hb ((∫⁻ w,V w ∂P)^(1/q)))

end Asakura.Chapter6

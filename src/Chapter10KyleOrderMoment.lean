import Chapter10OrderIntegrability
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

open MeasureTheory Set
namespace Asakura.Chapter10
set_option maxHeartbeats 1800000

/-- The exact singular square-mean bound for the equilibrium order rate. -/
theorem kyle_order_second_moment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (E : Ω → ℝ) (S0 T t l : ℝ)
    (hS : 0≤S0) (hT : 0<T) (ht : t<T) (hl : 0<l)
    (hvar : (∫ w,(E w)^2 ∂P)=S0*(T-t)/T) :
    Real.sqrt (∫ w,(E w/(l*(T-t)))^2 ∂P)=
      (Real.sqrt (S0/T)/l)*(T-t)^(-1/2:ℝ) := by
  have hdt : 0<T-t := sub_pos.mpr ht
  have he : (∫ w,(E w/(l*(T-t)))^2 ∂P)=(S0/T)/(l^2*(T-t)) := by
    simp_rw [div_pow]
    rw [integral_div,hvar]
    field_simp [hT.ne',hl.ne',hdt.ne']
  rw [he,Real.sqrt_div (div_nonneg hS hT.le),Real.sqrt_mul (sq_nonneg l),Real.sqrt_sq_eq_abs,
    abs_of_pos hl]
  have hp : (T-t)^(-1/2:ℝ)=(Real.sqrt (T-t))⁻¹ := by
    rw [show (-1/2:ℝ)=-(1/2) by norm_num,Real.rpow_neg hdt.le,Real.sqrt_eq_rpow]
  rw [hp]
  ring

end Asakura.Chapter10

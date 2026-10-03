import Chapter2CumulativeBound
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/-- Clipping an approximant to the range of the target cannot increase
its error, and makes the error uniformly bounded by twice that range. -/
theorem clipped_error_bounds (L x y : ℝ) (hL : 0 ≤ L) (hy : |y| ≤ L) :
    |max (-L) (min L x)-y| ≤ |x-y| ∧ |max (-L) (min L x)-y| ≤ 2*L := by
  have hy' := abs_le.1 hy
  have hc : -L ≤ max (-L) (min L x) ∧ max (-L) (min L x) ≤ L :=
    ⟨le_max_left _ _,max_le (by linarith) (min_le_left _ _)⟩
  refine ⟨?_,abs_le.2 ⟨by linarith [hc.1],by linarith [hc.2]⟩⟩
  by_cases hx : x ≤ -L
  · rw [min_eq_right (by linarith : x ≤ L),max_eq_left hx]
    rw [abs_of_nonpos (by linarith : -L-y ≤ 0),abs_of_nonpos (by linarith : x-y ≤ 0)]
    linarith
  · by_cases hxl : L ≤ x
    · rw [min_eq_left hxl,max_eq_right (by linarith : -L ≤ L)]
      rw [abs_of_nonneg (by linarith : 0 ≤ L-y),abs_of_nonneg (by linarith : 0 ≤ x-y)]
      linarith
    · rw [min_eq_right (not_le.1 hxl).le,max_eq_right (not_le.1 hx).le]

/-- The p>2 estimate in the density proof, with integrability derived
from the square integral rather than assumed. -/
theorem bounded_rpow_integral_le_square
    {S : Type*} [MeasurableSpace S] (μ : Measure S) (f : S → ℝ)
    (hf : AEStronglyMeasurable f μ) (h2 : Integrable (fun x => f x ^ 2) μ)
    (C p : ℝ) (hC : 0 ≤ C) (hp : 2 ≤ p) (hb : ∀ᵐ x ∂μ, |f x| ≤ C) :
    Integrable (fun x => |f x| ^ p) μ ∧
    (∫ x, |f x| ^ p ∂μ) ≤ C ^ (p-2) * ∫ x, f x ^ 2 ∂μ := by
  have he : ∀ᵐ x ∂μ, |f x| ^ p ≤ C ^ (p-2) * f x ^ 2 := by
    filter_upwards [hb] with x hx
    have hr : |f x| ^ p = |f x| ^ (p-2) * f x ^ 2 := by
      calc
        _ = |f x| ^ ((p-2)+2) := by congr 1; ring
        _ = _ := by rw [Real.rpow_add' (abs_nonneg _) (by linarith : (p-2)+2 ≠ 0),Real.rpow_two,sq_abs]
    rw [hr]
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (abs_nonneg _) hx (by linarith)) (sq_nonneg _)
  have hm : AEStronglyMeasurable (fun x => |f x| ^ p) μ :=
    (Real.continuous_rpow_const (by linarith : 0 ≤ p)).comp_aestronglyMeasurable hf.norm
  have hi : Integrable (fun x => |f x| ^ p) μ := by
    apply (h2.const_mul (C^(p-2))).mono' hm
    filter_upwards [he] with x hx
    simpa only [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)] using hx
  refine ⟨hi,?_⟩
  exact (integral_mono_ae hi (h2.const_mul _) he).trans_eq (integral_const_mul _ _)

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.clipped_error_bounds
#print axioms Asakura.Chapter2Complete.bounded_rpow_integral_le_square

import Chapter8OrderTimeChange
import Mathlib.Order.Hom.WithTopBot
import Mathlib.Topology.Order.MonotoneContinuity

open MeasureTheory Set
open scoped Topology NNReal ENNReal
namespace Asakura.Chapter8
set_option backward.isDefEq.respectTransparency false
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7
noncomputable section

def halfTimeENNReal : HalfClosedTime ≃o ℝ≥0∞ where
  toFun t := t.val.toENNReal
  invFun s := ⟨(s:EReal),EReal.coe_ennreal_nonneg s,le_top⟩
  left_inv t := Subtype.ext (EReal.coe_toENNReal t.property.1)
  right_inv s := EReal.toENNReal_coe
  map_rel_iff' := by
    intro s t
    change s.val.toENNReal ≤ t.val.toENNReal ↔ s.val ≤ t.val
    rw [← EReal.coe_ennreal_le_coe_ennreal_iff,
      EReal.coe_toENNReal s.property.1,EReal.coe_toENNReal t.property.1]

def ennrealScale (a : ℝ) (ha : 0 < a) : ENNReal ≃o ENNReal where
  toFun t := ENNReal.ofReal a * t
  invFun t := (ENNReal.ofReal a)⁻¹ * t
  left_inv t := ENNReal.inv_mul_cancel_left (ENNReal.ofReal_pos.mpr ha).ne' ENNReal.ofReal_ne_top
  right_inv t := ENNReal.mul_inv_cancel_left (ENNReal.ofReal_pos.mpr ha).ne' ENNReal.ofReal_ne_top
  map_rel_iff' := by
    intro x y
    change ENNReal.ofReal a*x ≤ ENNReal.ofReal a*y ↔ x ≤ y
    constructor
    · intro h
      have hh : (ENNReal.ofReal a)⁻¹*(ENNReal.ofReal a*x) ≤
          (ENNReal.ofReal a)⁻¹*(ENNReal.ofReal a*y) := by gcongr
      simpa only [ENNReal.inv_mul_cancel_left (ENNReal.ofReal_pos.mpr ha).ne' ENNReal.ofReal_ne_top] using hh
    · intro h; gcongr

def linearClock (a : ℝ) (ha : 0 < a) : HalfClosedTime ≃o HalfClosedTime :=
  halfTimeENNReal.trans ((ennrealScale a ha).trans halfTimeENNReal.symm)

theorem linear_clock_continuous (a : ℝ) (ha : 0 < a) : Continuous (linearClock a ha) :=
  (linearClock a ha).continuous

theorem half_time_ennreal_finite (r : ℝ) (hr : 0 ≤ r) :
    halfTimeENNReal (realTimeClamp (T := (⊤:EReal)) r) = ENNReal.ofReal r := by
  change (realTimeClamp (T := (⊤:EReal)) r).val.toENNReal = _
  rw [real_time_clamp_eq r hr le_top,EReal.real_coe_toENNReal]

theorem linear_clock_finite (a : ℝ) (ha : 0 < a) (r : ℝ) (hr : 0 ≤ r) :
    linearClock a ha (realTimeClamp r) = realTimeClamp (a*r) := by
  apply halfTimeENNReal.injective
  dsimp only [linearClock,OrderIso.trans_apply]
  rw [halfTimeENNReal.apply_symm_apply]
  change ENNReal.ofReal a*halfTimeENNReal (realTimeClamp r) = halfTimeENNReal (realTimeClamp (a*r))
  rw [half_time_ennreal_finite r hr,half_time_ennreal_finite (a*r) (mul_nonneg ha.le hr),ENNReal.ofReal_mul ha.le]

end
end Asakura.Chapter8

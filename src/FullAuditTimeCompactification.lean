import FullAuditBVQuadratic
import Chapter2WrittenGridStopping
import Mathlib.Basic.ENNReal.Inv

open Set
open scoped ENNReal
namespace Asakura.FullAudit
open Asakura.Chapter2Written
set_option backward.isDefEq.respectTransparency false

/-- Nonnegative extended time, restricted at T, as an initial ENNReal interval. -/
noncomputable def closedTimeToENNReal {T : EReal} (hT : 0 ≤ T) :
    ClosedTime T ≃o Iic T.toENNReal where
  toFun t := ⟨t.val.toENNReal,EReal.toENNReal_le_toENNReal t.property.2⟩
  invFun u := ⟨(u.val:EReal),EReal.coe_ennreal_nonneg _,by
    have h := EReal.coe_ennreal_le_coe_ennreal_iff.mpr u.property
    simpa only [EReal.coe_toENNReal hT] using h⟩
  left_inv t := by apply Subtype.ext; exact EReal.coe_toENNReal t.property.1
  right_inv u := by apply Subtype.ext; exact EReal.toENNReal_coe
  map_rel_iff' := by
    intro s t
    constructor
    · intro h
      change s.val.toENNReal ≤ t.val.toENNReal at h
      have hh := EReal.coe_ennreal_le_coe_ennreal_iff.mpr h
      change s.val ≤ t.val
      simpa only [EReal.coe_toENNReal s.property.1,EReal.coe_toENNReal t.property.1] using hh
    · intro h
      exact EReal.toENNReal_le_toENNReal h

/-- Remove the nested subtype on the initial part of the unit interval. -/
noncomputable def unitInitialFlatten (u : UnitTime) : Iic u ≃o Icc (0:ℝ) u.val where
  toFun x := ⟨x.val.val,x.val.property.1,x.property⟩
  invFun x := ⟨⟨x.val,x.property.1,x.property.2.trans u.property.2⟩,x.property.2⟩
  left_inv x := rfl
  right_inv x := rfl
  map_rel_iff' := Iff.rfl

noncomputable def positiveIntervalScale (a : ℝ) (ha : 0 < a) : UnitTime ≃o Icc (0:ℝ) a where
  toFun x := ⟨a*x.val,mul_nonneg ha.le x.property.1,by nlinarith [x.property.2]⟩
  invFun x := ⟨x.val/a,div_nonneg x.property.1 ha.le,(div_le_one ha).mpr x.property.2⟩
  left_inv x := by apply Subtype.ext; simp [ha.ne']
  right_inv x := by apply Subtype.ext; dsimp; field_simp
  map_rel_iff' := by intro x y; exact mul_le_mul_iff_right₀ ha

/-- Explicit compactification for every nontrivial [0,T], including infinity.
 It uses the order isomorphism x ↦ x/(1+x) followed by a positive rescaling. -/
noncomputable def closedTimeUnitIso {T : EReal} (hT : 0 < T) : UnitTime ≃o ClosedTime T := by
  let e := ENNReal.orderIsoUnitIntervalBirational
  let u := e T.toENNReal
  have hu : 0 < u.val := by
    have ht : (0:ℝ≥0∞) < T.toENNReal := EReal.toENNReal_pos_iff.mpr hT
    have hh : (⊥:UnitTime) < u := by
      have h := e.strictMono ht
      change e ⊥ < e T.toENNReal at h
      rw [e.map_bot] at h
      exact h
    exact hh
  exact ((closedTimeToENNReal hT.le).trans ((e.Iic T.toENNReal).trans
    ((unitInitialFlatten u).trans (positiveIntervalScale u.val hu).symm))).symm

end Asakura.FullAudit

import Chapter12FiniteCompactTime

open MeasureTheory Set
open scoped ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false

theorem compact_finite_time_inverse (T : ℝ) (hT : 0≤T)
    (f : Lp ℝ 2 (compactTimeMeasure T hT)) :
    finiteTimeToCompact T hT (compactTimeToFinite T hT f)=f := by
  have h := (compact_time_val_preserving T hT).quasiMeasurePreserving.ae_eq_comp
    (Lp.coeFn_compMeasurePreserving f (compact_time_proj_preserving T hT))
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving (compactTimeToFinite T hT f)
    (compact_time_val_preserving T hT),h] with t ht hh
  change finiteTimeToCompact T hT (compactTimeToFinite T hT f) t=f t
  change finiteTimeToCompact T hT (compactTimeToFinite T hT f) t=
    compactTimeToFinite T hT f t.val at ht
  rw [ht]
  change compactTimeToFinite T hT f t.val=f (projIcc 0 T hT t.val) at hh
  rw [hh,projIcc_of_mem hT t.property]

theorem finite_compact_time_inverse (T : ℝ) (hT : 0≤T)
    (f : Lp ℝ 2 ((volume.restrict (Ioi (0:ℝ))).restrict (Iic T))) :
    compactTimeToFinite T hT (finiteTimeToCompact T hT f)=f := by
  apply (finiteTimeToCompact T hT).injective
  exact compact_finite_time_inverse T hT _

end Asakura.Chapter12

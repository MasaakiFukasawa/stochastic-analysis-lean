import Chapter12WienerIncrementFromCoordinates

open MeasureTheory Set
open scoped ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

theorem finite_time_interval_norm (T a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T) :
    ‖finiteTimeIntervalVector T a b‖ = Real.sqrt (b-a) := by
  have hm : ((volume.restrict (Ioi (0:ℝ))).restrict (Iic T)) (Ioc a b) = ENNReal.ofReal (b-a) := by
    rw [Measure.restrict_apply measurableSet_Ioc]
    rw [inter_eq_left.mpr (show Ioc a b ⊆ Iic T from fun _ h => h.2.trans hb)]
    rw [Measure.restrict_apply measurableSet_Ioc]
    rw [inter_eq_left.mpr (show Ioc a b ⊆ Ioi 0 from fun _ h => ha.trans_lt h.1)]
    exact Real.volume_Ioc
  unfold finiteTimeIntervalVector
  rw [norm_indicatorConstLp (by norm_num) (by norm_num)]
  simp only [norm_one,one_mul,Measure.real,hm,ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]
  norm_num [Real.sqrt_eq_rpow]

theorem finite_time_prefix_dist (T : ℝ) (s t : Icc (0:ℝ) T) :
    dist (finiteTimeIntervalVector T 0 s.val) (finiteTimeIntervalVector T 0 t.val) =
      Real.sqrt (dist s.val t.val) := by
  rcases le_total s.val t.val with hst | hts
  · rw [dist_eq_norm,norm_sub_rev,finite_time_interval_difference T s.val t.val s.property.1 hst,
      finite_time_interval_norm T s.val t.val s.property.1 hst t.property.2]
    rw [Real.dist_eq,abs_sub_comm,abs_of_nonneg (sub_nonneg.mpr hst)]
  · rw [dist_eq_norm,finite_time_interval_difference T t.val s.val t.property.1 hts,
      finite_time_interval_norm T t.val s.val t.property.1 hts s.property.2]
    rw [Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr hts)]

/-- The prefix indicator is continuous in the deterministic L2 time norm,
although its pointwise values have jumps as functions of the endpoint. -/
theorem finite_time_prefix_continuous (T : ℝ) :
    Continuous (fun t : Icc (0:ℝ) T => finiteTimeIntervalVector T 0 t.val) := by
  apply continuous_iff_continuousAt.mpr
  intro s
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  refine ⟨ε^2,sq_pos_of_pos hε,fun t ht => ?_⟩
  rw [finite_time_prefix_dist]
  exact (Real.sqrt_lt' hε).mpr ht

end Asakura.Chapter12

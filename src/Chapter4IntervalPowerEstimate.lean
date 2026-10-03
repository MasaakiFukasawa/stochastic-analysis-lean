import Chapter4PowerGrowth

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter4
set_option maxHeartbeats 1500000

lemma interval_integral_power_holder (t : ℝ) (ht : 0≤t)
    (f : ℝ → ℝ) (hf : ∀ r,0≤f r) (q : ℝ) (hq : 1≤q)
    (hi : IntervalIntegrable (fun r => f r^q) volume 0 t) :
    IntervalIntegrable f volume 0 t ∧
      (∫ r in 0..t,f r)^q≤t^(q-1)*(∫ r in 0..t,f r^q) := by
  obtain ⟨hi',hb⟩ := integral_power_holder (volume.restrict (Ioc (0:ℝ) t)) f hf q hq hi.1
  have hm : (volume.restrict (Ioc (0:ℝ) t)).real univ=t := by
    simp only [measureReal_def,Measure.restrict_apply_univ,Real.volume_Ioc,sub_zero,ENNReal.toReal_ofReal ht]
  rw [hm] at hb
  refine ⟨⟨hi',?_⟩,?_⟩
  · change Integrable f (volume.restrict (Ioc t 0))
    rw [Ioc_eq_empty_of_le ht,Measure.restrict_empty]
    exact integrable_zero_measure
  · simpa only [intervalIntegral.integral_of_le ht] using hb

/-- Jensen/Hölder followed by the coefficient-growth bound. The stopped
coefficient may be only measurable; continuity is not required. -/
theorem interval_power_from_growth (t : ℝ) (ht : 0≤t)
    (H U : ℝ → ℝ) (hH : ∀ r,0≤H r) (q : ℝ) (hq : 1≤q)
    (hiH : IntervalIntegrable (fun r => H r^q) volume 0 t)
    (hiU : IntervalIntegrable U volume 0 t)
    (K : ℝ) (hb : ∀ r∈Icc 0 t,H r^q≤K*U r) :
    (∫ r in 0..t,H r)^q≤(t^(q-1)*K)*(∫ r in 0..t,U r) := by
  have hh := (interval_integral_power_holder t ht H hH q hq hiH).2
  have hu : (∫ r in 0..t,H r^q)≤K*(∫ r in 0..t,U r) := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_mono_on ht hiH (hiU.const_mul K) hb
  exact hh.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hu (Real.rpow_nonneg ht _))

end Asakura.Chapter4

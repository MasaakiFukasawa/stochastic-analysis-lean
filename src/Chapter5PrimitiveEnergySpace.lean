import Chapter5TimePrimitiveL2

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter2Complete
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

theorem prefix_time_integral_square_bound (R : ℝ) (hR : 0 ≤ R)
    (f : ℝ → ℝ) (hf : MemLp f 2 (volume.restrict (Ioc 0 R)))
    (t : ℝ) (ht : t ∈ Icc 0 R) :
    (∫ r in 0..t,f r)^2 ≤ R*(∫ r in 0..R,f r^2) := by
  have hh := cumulative_integral_square_bound (volume.restrict (Ioc 0 R)) f hf (Ioc 0 t)
  rw [Measure.restrict_restrict measurableSet_Ioc,inter_eq_left.mpr (Ioc_subset_Ioc_right ht.2)] at hh
  have hm : (volume.restrict (Ioc 0 R)).real univ = R := by
    simp [Measure.real,Real.volume_Ioc,ENNReal.toReal_ofReal hR]
  rw [hm,Real.norm_eq_abs,sq_abs] at hh
  simpa only [intervalIntegral.integral_of_le ht.1,intervalIntegral.integral_of_le hR] using hh

/-- The primitive belongs to the sample-time L² space, not merely to L²
at each fixed time. This is needed for the frozen BSDE map's codomain. -/
theorem time_primitive_sample_time_memLp_two
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (R : ℝ) (hR : 0 ≤ R) (H : Ω × ℝ → ℝ) (hH : Measurable H)
    (hi : MemLp H 2 (P.prod (volume.restrict (Ioc 0 R)))) :
    MemLp (fun z : Ω × ℝ => ∫ r in 0..z.2,H (z.1,r)) 2 (P.prod (volume.restrict (Ioc 0 R))) := by
  obtain ⟨hsec,henergy⟩ := finite_time_L2_sections P R hR H hH hi
  have hm := time_primitive_joint_measurable H hH
  have hEm : Measurable (fun w => ∫ r in 0..R,H (w,r)^2) := by
    simpa only [intervalIntegral.integral_of_le hR] using
      ((hH.pow_const 2).stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ioc 0 R))).measurable
  apply (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr
  apply ((henergy.const_mul R).comp_fst (volume.restrict (Ioc 0 R))).mono' (hm.pow_const 2).aestronglyMeasurable
  have hb : ∀ᵐ z ∂P.prod (volume.restrict (Ioc 0 R)),
      (∫ r in 0..z.2,H (z.1,r))^2 ≤ R*(∫ r in 0..R,H (z.1,r)^2) := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_le (hm.pow_const 2) ((hEm.const_mul R).comp measurable_fst))).mpr
    filter_upwards [hsec] with w hw
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact prefix_time_integral_square_bound R hR (fun r => H (w,r)) hw t ⟨ht.1.le,ht.2⟩
  filter_upwards [hb] with z hz
  simpa only [Real.norm_eq_abs,abs_sq] using hz

end Asakura.Chapter5

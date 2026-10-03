import Chapter5ProgressivePrimitive
import Chapter5BSDEMaximal

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter2Complete
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- Joint measurability of the actual ordinary primitive, including the
parameter giving its upper endpoint. -/
theorem time_primitive_joint_measurable
    {Ω : Type*} [MeasurableSpace Ω] (H : Ω × ℝ → ℝ) (hH : Measurable H) :
    Measurable (fun z : Ω × ℝ => ∫ r in 0..z.2,H (z.1,r)) := by
  classical
  have hg : Measurable (fun q : (Ω × ℝ) × ℝ => H (q.1.1,q.2)) :=
    hH.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  have hp : Measurable (fun q : (Ω × ℝ) × ℝ => if 0 < q.2 ∧ q.2 ≤ q.1.2 then H (q.1.1,q.2) else 0) :=
    Measurable.ite ((measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd (measurable_snd.comp measurable_fst))) hg measurable_const
  have hn : Measurable (fun q : (Ω × ℝ) × ℝ => if q.1.2 < q.2 ∧ q.2 ≤ 0 then H (q.1.1,q.2) else 0) :=
    Measurable.ite ((measurableSet_lt (measurable_snd.comp measurable_fst) measurable_snd).inter
      (measurableSet_le measurable_snd measurable_const)) hg measurable_const
  have hh := (hp.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable.sub
    (hn.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable
  convert hh using 1
  funext z
  rw [intervalIntegral,← integral_indicator measurableSet_Ioc,← integral_indicator measurableSet_Ioc]
  simp only [Set.indicator,mem_Ioc,Pi.sub_apply]

/-- Every prefix integral has an L² bound from the same sample-time L²
driver. In particular the terminal variable used in conditional
expectation is square integrable. -/
theorem time_primitive_memLp_two
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (R : ℝ) (hR : 0 ≤ R) (H : Ω × ℝ → ℝ) (hH : Measurable H)
    (hi : MemLp H 2 (P.prod (volume.restrict (Ioc 0 R))))
    (t : ℝ) (ht : t ∈ Icc 0 R) :
    MemLp (fun w => ∫ r in 0..t,H (w,r)) 2 P := by
  obtain ⟨hsec,henergy⟩ := finite_time_L2_sections P R hR H hH hi
  have hm : Measurable (fun w => ∫ r in 0..t,H (w,r)) :=
    (time_primitive_joint_measurable H hH).comp (measurable_id.prodMk measurable_const)
  apply (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr
  apply (henergy.const_mul R).mono' (hm.pow_const 2).aestronglyMeasurable
  filter_upwards [hsec] with w hw
  have hh := cumulative_integral_square_bound (volume.restrict (Ioc 0 R)) (fun r => H (w,r)) hw (Ioc 0 t)
  rw [Measure.restrict_restrict measurableSet_Ioc,inter_eq_left.mpr (Ioc_subset_Ioc_right ht.2)] at hh
  have hmass : (volume.restrict (Ioc 0 R)).real univ = R := by
    simp [Measure.real,Real.volume_Ioc,ENNReal.toReal_ofReal hR]
  rw [hmass,Real.norm_eq_abs,sq_abs] at hh
  simpa only [Real.norm_eq_abs,abs_sq,intervalIntegral.integral_of_le ht.1,intervalIntegral.integral_of_le hR] using hh

end Asakura.Chapter5

import Chapter13ParameterEnergyReorder
import Chapter13MaturityCutoff

open MeasureTheory Set
namespace Asakura.Chapter13
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

/-- Pathwise identification of the stopped parameter energy with the
accumulated energy at the stopping time. -/
theorem parameter_stopped_energy {E:Type*} [MeasurableSpace E]
    (μ:Measure E) [SigmaFinite μ] (R q:ℝ) (hq:q∈Icc 0 R)
    (H:E × ℝ → ℝ)
    (hi:Integrable (fun z => H z^2) (μ.prod (volume.restrict (Ioc 0 R)))) :
    let K:=fun z:E × ℝ => (Ioc 0 q).indicator (fun r => H (z.1,r)) z.2
    Integrable (fun z => K z^2) (μ.prod (volume.restrict (Ioi 0))) ∧
      (∫z,K z^2∂μ.prod (volume.restrict (Ioi 0)))=∫r in 0..q,∫x,H (x,r)^2∂μ := by
  intro K
  let S:Set (E × ℝ):=univ ×ˢ Ioc 0 q
  have hS:MeasurableSet S := MeasurableSet.univ.prod measurableSet_Ioc
  have he:(fun z => K z^2)=S.indicator (fun z => H z^2) := by
    funext z
    simp only [K,S,mem_prod,mem_univ,true_and,indicator_apply]
    split_ifs <;> simp
  have hmeasure:(μ.prod (volume.restrict (Ioi 0))).restrict S=μ.prod (volume.restrict (Ioc 0 q)) := by
    change (μ.prod (volume.restrict (Ioi 0))).restrict (univ ×ˢ Ioc 0 q) = _
    rw [←Measure.prod_restrict,Measure.restrict_univ,Measure.restrict_restrict measurableSet_Ioc]
    congr 2
    exact inter_eq_left.mpr (fun _ h => h.1)
  have hiq:Integrable (fun z => H z^2) (μ.prod (volume.restrict (Ioc 0 q))) :=
    hi.mono_measure (Measure.prod_mono le_rfl (Measure.restrict_mono (Ioc_subset_Ioc_right hq.2) le_rfl))
  rw [he]
  constructor
  · apply (integrable_indicator_iff hS).mpr
    change Integrable _ ((μ.prod (volume.restrict (Ioi 0))).restrict S)
    rwa [hmeasure]
  · rw [integral_indicator hS,hmeasure,integral_prod_symm _ hiq,intervalIntegral.integral_of_le hq.1]
end Asakura.Chapter13
#print axioms Asakura.Chapter13.parameter_stopped_energy

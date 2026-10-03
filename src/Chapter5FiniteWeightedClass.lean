import Chapter5WeightedRealizationNorm
import Chapter5ProgressivePrefixRestriction

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false

noncomputable def finiteWeightedClass
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (F : ClosedTime T → MeasurableSpace Ω)
    (R β : ℝ) (hR : 0≤R) (hβ : 0≤β)
    (H : Ω × ℝ → ℝ) (hHm : Measurable H)
    (hHp : @Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) R => F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) R => H (z.1,z.2.val)))
    (hH : MemLp H 2 (P.prod (volume.restrict (Ioc 0 R)))) :
    progressiveEnergyRange F (fun _ => R) (exponentialEnergyMeasure (P.prod (volume.restrict (Ioc 0 R))) β) := by
  let μ := exponentialEnergyMeasure (P.prod (volume.restrict (Ioc 0 R))) β
  have hw : MemLp H 2 μ := (finite_weighted_memLp_two_iff P R hR β hβ H hHm).mpr hH
  exact ⟨hw.toLp H,⟨⟨H,hHm,(fun _ => hHp),hw⟩,rfl⟩⟩

lemma finite_weighted_representative
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (F : ClosedTime T → MeasurableSpace Ω)
    (R β : ℝ) (hR : 0≤R) (hβ : 0≤β)
    (x : progressiveEnergyRange F (fun _ => R) (exponentialEnergyMeasure (P.prod (volume.restrict (Ioc 0 R))) β)) :
    ∃ H : Ω × ℝ → ℝ,∃ hm : Measurable H,
      ∃ hp : @Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) R => F (realTimeClamp t.val))) inferInstance
        (fun z : Ω × Icc (0:ℝ) R => H (z.1,z.2.val)),
      ∃ hi : MemLp H 2 (P.prod (volume.restrict (Ioc 0 R))),
        finiteWeightedClass P F R β hR hβ H hm hp hi=x := by
  obtain ⟨H,he⟩ := x.property
  let hi := (finite_weighted_memLp_two_iff P R hR β hβ H.val H.property.1).mp H.property.2.2
  refine ⟨H.val,H.property.1,H.property.2.1 0,hi,?_⟩
  apply Subtype.ext
  exact he

lemma finite_weighted_class_difference_norm
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (F : ClosedTime T → MeasurableSpace Ω)
    (R β : ℝ) (hR : 0≤R) (hβ : 0≤β)
    (H G : Ω × ℝ → ℝ) (hHm : Measurable H) (hGm : Measurable G)
    (hHp : @Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) R => F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) R => H (z.1,z.2.val)))
    (hGp : @Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) R => F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) R => G (z.1,z.2.val)))
    (hH : MemLp H 2 (P.prod (volume.restrict (Ioc 0 R))))
    (hG : MemLp G 2 (P.prod (volume.restrict (Ioc 0 R)))) :
    ‖finiteWeightedClass P F R β hR hβ H hHm hHp hH-finiteWeightedClass P F R β hR hβ G hGm hGp hG‖^2=
      ∫ w,(∫ r in 0..R,Real.exp (β*r)*(H (w,r)-G (w,r))^2) ∂P := by
  have hwH := (finite_weighted_memLp_two_iff P R hR β hβ H hHm).mpr hH
  have hwG := (finite_weighted_memLp_two_iff P R hR β hβ G hGm).mpr hG
  change ‖hwH.toLp H-hwG.toLp G‖^2=_
  rw [← MemLp.toLp_sub hwH hwG]
  exact weighted_realization_norm_sq P R β hR hβ _ (hHm.sub hGm) (hwH.sub hwG)

end Asakura.Chapter5

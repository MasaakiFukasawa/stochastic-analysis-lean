import Chapter5FiniteWeightedClass
import Chapter5FrozenFiniteEnergyData
import Chapter5RelationalFixedPoint

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

structure FiniteProgressiveProcess
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω)
    {T : EReal} [Fact (0≤T)] (F : ClosedTime T → MeasurableSpace Ω) (R : ℝ) where
  value : Ω × ℝ → ℝ
  measurable : Measurable value
  progressive : @Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) R => F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) R => value (z.1,z.2.val))
  energy : MemLp value 2 (P.prod (volume.restrict (Ioc 0 R)))

noncomputable def FiniteProgressiveProcess.realize
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (F : ClosedTime T → MeasurableSpace Ω)
    (R β : ℝ) (hR : 0≤R) (hβ : 0≤β) (u : FiniteProgressiveProcess P F R) :=
  finiteWeightedClass P F R β hR hβ u.value u.measurable u.progressive u.energy

lemma finite_progressive_realize_surjective
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (F : ClosedTime T → MeasurableSpace Ω)
    (R β : ℝ) (hR : 0≤R) (hβ : 0≤β) :
    Function.Surjective (FiniteProgressiveProcess.realize P F R β hR hβ) := by
  intro x
  obtain ⟨H,hm,hp,hi,he⟩ := finite_weighted_representative P F R β hR hβ x
  exact ⟨⟨H,hm,hp,hi⟩,he⟩

lemma FiniteProgressiveProcess.difference_norm
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (F : ClosedTime T → MeasurableSpace Ω)
    (R β : ℝ) (hR : 0≤R) (hβ : 0≤β) (u v : FiniteProgressiveProcess P F R) :
    ‖u.realize P F R β hR hβ-v.realize P F R β hR hβ‖^2=
      ∫ w,(∫ r in 0..R,Real.exp (β*r)*(u.value (w,r)-v.value (w,r))^2) ∂P :=
  finite_weighted_class_difference_norm P F R β hR hβ u.value v.value u.measurable v.measurable
    u.progressive v.progressive u.energy v.energy

lemma FiniteProgressiveProcess.realize_eq_iff
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (F : ClosedTime T → MeasurableSpace Ω)
    (R β : ℝ) (hR : 0≤R) (hβ : 0≤β) (u v : FiniteProgressiveProcess P F R) :
    u.realize P F R β hR hβ=v.realize P F R β hR hβ ↔
      u.value =ᵐ[P.prod (volume.restrict (Ioc 0 R))] v.value := by
  have hu := (finite_weighted_memLp_two_iff P R hR β hβ u.value u.measurable).mpr u.energy
  have hv := (finite_weighted_memLp_two_iff P R hR β hβ v.value v.measurable).mpr v.energy
  constructor
  · intro he
    have he' : hu.toLp u.value=hv.toLp v.value := congrArg Subtype.val he
    exact (exponential_energy_ae_iff _ β _).mp ((MemLp.toLp_eq_toLp_iff hu hv).mp he')
  · intro he
    apply Subtype.ext
    exact (MemLp.toLp_eq_toLp_iff hu hv).mpr ((exponential_energy_ae_iff _ β _).mpr he)

noncomputable def BSDEFiniteEnergyData.outputY
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (F : ClosedTime T → MeasurableSpace Ω)
    (W : ClosedTime T → Ω → ℝ) (c : ℕ → ℝ) (R : ℝ)
    (u : BSDEFiniteEnergyData P F W c R)
    (hp : @Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) R => F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) R => u.Y (realTimeClamp z.2.val) z.1)) : FiniteProgressiveProcess P F R :=
  ⟨fun z => u.Y (realTimeClamp z.2) z.1,u.measurableY,hp,u.energyY⟩

noncomputable def BSDEFiniteEnergyData.outputZ
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (F : ClosedTime T → MeasurableSpace Ω)
    (W : ClosedTime T → Ω → ℝ) (c : ℕ → ℝ) (hco : ∀ r,∃ j,r≤c j) (R : ℝ)
    (u : BSDEFiniteEnergyData P F W c R) : FiniteProgressiveProcess P F R := by
  let j := Classical.choose (hco R)
  have hj : R≤c j := Classical.choose_spec (hco R)
  exact ⟨u.Z,u.measurableZ,
    progressive_real_prefix_restriction (fun r => F (realTimeClamp r)) u.Z R (c j) hj (u.progressiveZ j),u.energyZ⟩

end Asakura.Chapter5

import Chapter2ProgressiveEnergySpace
import Mathlib.MeasureTheory.Measure.Prod

open MeasureTheory Set
open scoped ENNReal
namespace Asakura.Chapter12
open Asakura.FullAudit Asakura.Chapter2Written Asakura.Chapter2Complete
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

/-- Deterministic L2 time functions embed isometrically into the actual
progressive L2 space used by the constructed Ito integral. -/
noncomputable def deterministicEnergyEmbedding
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (c : ℕ → ℝ) : Lp ℝ 2 (volume.restrict (Ioi (0:ℝ))) →ₗᵢ[ℝ]
      progressiveEnergyRange F c (P.prod (volume.restrict (Ioi (0:ℝ)))) := by
  let μ := volume.restrict (Ioi (0:ℝ))
  let J : Lp ℝ 2 μ →ₗᵢ[ℝ] Lp ℝ 2 (P.prod μ) :=
    Lp.compMeasurePreservingₗᵢ ℝ Prod.snd (measurePreserving_snd (μ := P) (ν := μ))
  have hj (f : Lp ℝ 2 μ) : J f ∈ progressiveEnergyRange F c (P.prod μ) := by
    have hm : Measurable (fun z : Ω × ℝ => f z.2) := (Lp.stronglyMeasurable f).measurable.comp measurable_snd
    have hp n : @Measurable _ _
        (progressiveSpace (fun t : Icc (0:ℝ) (c n) => F (realTimeClamp t.val))) inferInstance
        (fun z : Ω × Icc (0:ℝ) (c n) => f z.2.val) := by
      apply (measurable_progressive_iff _ _).mpr
      intro t
      exact (Lp.stronglyMeasurable f).measurable.comp
        (measurable_subtype_coe.comp (measurable_subtype_coe.comp measurable_snd))
    have hi : MemLp (fun z : Ω × ℝ => f z.2) 2 (P.prod μ) :=
      (Lp.memLp f).comp_measurePreserving (measurePreserving_snd (μ := P) (ν := μ))
    let G : progressiveEnergyIntegrands F c (P.prod μ) := ⟨_,hm,hp,hi⟩
    refine ⟨G,?_⟩
    apply Lp.ext
    exact hi.coeFn_toLp.trans (Lp.coeFn_compMeasurePreserving f
      (measurePreserving_snd (μ := P) (ν := μ))).symm
  exact { toLinearMap := J.toLinearMap.codRestrict _ hj
          norm_map' := fun f => J.norm_map f }

/-- The deterministic representative is progressive for every filtration. -/
noncomputable def deterministicEnergyIntegrand
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (c : ℕ → ℝ) (f : Lp ℝ 2 (volume.restrict (Ioi (0:ℝ)))) :
    progressiveEnergyIntegrands F c (P.prod (volume.restrict (Ioi (0:ℝ)))) := by
  refine ⟨fun z => f z.2, (Lp.stronglyMeasurable f).measurable.comp measurable_snd,?_,?_⟩
  · intro n
    apply (measurable_progressive_iff _ _).mpr
    intro t
    exact (Lp.stronglyMeasurable f).measurable.comp
      (measurable_subtype_coe.comp (measurable_subtype_coe.comp measurable_snd))
  · exact (Lp.memLp f).comp_measurePreserving (measurePreserving_snd (μ := P)
      (ν := volume.restrict (Ioi (0:ℝ))))

/-- Its representative is the deterministic integrand, for the product
measure used in the Ito isometry. -/
theorem deterministic_energy_coe {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {T : EReal} [Fact (0 ≤ T)]
    (F : ClosedTime T → MeasurableSpace Ω) (c : ℕ → ℝ)
    (f : Lp ℝ 2 (volume.restrict (Ioi (0:ℝ)))) :
    ((deterministicEnergyEmbedding P F c f).val : Ω × ℝ → ℝ) =ᵐ[P.prod (volume.restrict (Ioi (0:ℝ)))]
      fun z => f z.2 :=
  Lp.coeFn_compMeasurePreserving f (measurePreserving_snd (μ := P) (ν := volume.restrict (Ioi (0:ℝ))))

theorem deterministic_energy_realization {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {T : EReal} [Fact (0 ≤ T)]
    (F : ClosedTime T → MeasurableSpace Ω) (c : ℕ → ℝ)
    (f : Lp ℝ 2 (volume.restrict (Ioi (0:ℝ)))) :
    deterministicEnergyEmbedding P F c f =
      ⟨progressiveEnergyToLp F c _ (deterministicEnergyIntegrand P F c f),
        LinearMap.mem_range_self _ _⟩ := by
  apply Subtype.ext
  apply Lp.ext
  exact (deterministic_energy_coe P F c f).trans
    (deterministicEnergyIntegrand P F c f).property.2.2.coeFn_toLp.symm

end Asakura.Chapter12

import Chapter12DeterministicEnergy

open MeasureTheory Set
open scoped ENNReal
namespace Asakura.Chapter12
open Asakura.FullAudit Asakura.Chapter2Written Asakura.Chapter2Complete
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

/-- Use any measurable representative of a deterministic L2 function in
the progressive energy space. -/
noncomputable def rawDeterministicEnergyIntegrand
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (c : ℕ → ℝ) (f : ℝ → ℝ) (hm : Measurable f)
    (hi : MemLp f 2 (volume.restrict (Ioi (0:ℝ)))) :
    progressiveEnergyIntegrands F c (P.prod (volume.restrict (Ioi (0:ℝ)))) := by
  refine ⟨fun z => f z.2,hm.comp measurable_snd,?_,?_⟩
  · intro n
    apply (measurable_progressive_iff _ _).mpr
    intro t
    exact hm.comp (measurable_subtype_coe.comp (measurable_subtype_coe.comp measurable_snd))
  · exact hi.comp_measurePreserving (measurePreserving_snd (μ := P) (ν := volume.restrict (Ioi (0:ℝ))))

theorem raw_deterministic_energy_realization
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (c : ℕ → ℝ) (f : ℝ → ℝ) (hm : Measurable f)
    (hi : MemLp f 2 (volume.restrict (Ioi (0:ℝ)))) :
    deterministicEnergyEmbedding P F c (hi.toLp f) =
      ⟨progressiveEnergyToLp F c _ (rawDeterministicEnergyIntegrand P F c f hm hi),
        LinearMap.mem_range_self _ _⟩ := by
  apply Subtype.ext
  apply Lp.ext
  refine (deterministic_energy_coe P F c (hi.toLp f)).trans ?_
  have he : (fun z : Ω × ℝ => hi.toLp f z.2) =ᵐ[P.prod (volume.restrict (Ioi (0:ℝ)))]
      fun z => f z.2 := (measurePreserving_snd (μ := P) (ν := volume.restrict (Ioi (0:ℝ)))).quasiMeasurePreserving.ae_eq hi.coeFn_toLp
  exact he.trans (rawDeterministicEnergyIntegrand P F c f hm hi).property.2.2.coeFn_toLp.symm

end Asakura.Chapter12

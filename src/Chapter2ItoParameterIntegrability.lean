import Chapter2ActualItoOperator
import Chapter2L2SectionIntegrable

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

/-- The parameter family takes values in the actual progressive L2 domain.
Composing the constructed Ito isometry therefore yields an integrable M2
family, with exactly the mixed norm in the printed stochastic-Fubini theorem. -/
theorem ito_parameter_family_integrable
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω) (c : ℕ → ℝ)
    (μ : Measure E) (ν : Measure (Ω × ℝ)) [SigmaFinite ν]
    (L : progressiveEnergyRange F c ν →ₗᵢ[ℝ] continuousM2Terminal P F)
    (H : E × (Ω × ℝ) → ℝ) (hH : Measurable H)
    (hp : ∀ x n, @Measurable _ _
      (progressiveSpace (fun t : Icc (0:ℝ) (c n) => F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) (c n) => H (x,(z.1,z.2.val))))
    (hN : (∫⁻ x, eLpNorm (fun z => H (x,z)) 2 ν ∂μ) < ∞) :
    ∃ U : E → progressiveEnergyRange F c ν,
      (∀ x, (U x : Lp ℝ 2 ν) = l2Section ν H x) ∧
      StronglyMeasurable U ∧ Integrable U μ ∧ Integrable (fun x => L (U x)) μ ∧
      (∫ x, ‖L (U x)‖ ∂μ) = ∫ x, (eLpNorm (fun z => H (x,z)) 2 ν).toReal ∂μ := by
  classical
  have hmem x : l2Section ν H x ∈ progressiveEnergyRange F c ν := by
    by_cases hx : MemLp (fun z => H (x,z)) 2 ν
    · let g : progressiveEnergyIntegrands F c ν :=
        ⟨fun z => H (x,z),hH.comp measurable_prodMk_left,hp x,hx⟩
      refine ⟨g,?_⟩
      simp only [l2Section,dif_pos hx]
      rfl
    · simp only [l2Section,dif_neg hx]
      exact (progressiveEnergyRange F c ν).zero_mem
  let U := fun x => (⟨l2Section ν H x,hmem x⟩ : progressiveEnergyRange F c ν)
  have hUm : StronglyMeasurable U := by
    apply (Embedding.comp_stronglyMeasurable_iff Topology.IsEmbedding.subtypeVal).mp
    exact stronglyMeasurable_l2Section ν H hH
  obtain ⟨hI,_,hnorm⟩ := integrable_l2Section μ ν H hH hN
  have hUI : Integrable U μ := ⟨hUm.aestronglyMeasurable,hI.hasFiniteIntegral⟩
  refine ⟨U,fun _ => rfl,hUm,hUI,L.toContinuousLinearMap.integrable_comp hUI,?_⟩
  simp only [L.norm_map]
  exact hnorm

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.ito_parameter_family_integrable

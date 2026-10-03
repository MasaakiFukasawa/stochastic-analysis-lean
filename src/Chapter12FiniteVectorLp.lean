import Chapter12CylinderLp
import Mathlib.MeasureTheory.Function.FactorsThrough

open MeasureTheory Set Filter
open scoped ContDiff ENNReal Topology
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false

theorem finite_vector_smooth_Lp {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hpt : p ≠ ⊤)
    (X : Ω → E) (hX : Measurable X) (U : Lp ℝ p P)
    (hU : AEStronglyMeasurable[MeasurableSpace.comap X inferInstance] U P)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (g : E → ℝ) (hg : MemLp (g ∘ X) p P),
      HasCompactSupport g ∧ ContDiff ℝ ∞ g ∧
      ‖U - hg.toLp (g ∘ X)‖ ≤ ε := by
  obtain ⟨f,hf,he⟩ := hU.stronglyMeasurable_mk.measurable.exists_eq_measurable_comp
  have hUf : (U : Ω → ℝ) =ᵐ[P] f ∘ X := by
    simpa only [he] using hU.ae_eq_mk
  have hi : MemLp (f ∘ X) p P := (Lp.memLp U).ae_eq hUf
  obtain ⟨g,hgc,hgd,_,hge⟩ := smooth_cylinder_Lp_approximation P X hX f hf p hpt (Fact.out : 1 ≤ p) hi ε hε
  obtain ⟨B,hB⟩ := hgc.isCompact_range hgd.continuous |>.exists_bound_of_continuousOn
    continuous_id.continuousOn
  have hgi : MemLp (g ∘ X) p P := MemLp.of_bound
    (hgd.continuous.measurable.comp hX).aestronglyMeasurable B
    (ae_of_all _ fun w => hB _ ⟨X w,rfl⟩)
  refine ⟨g,hgi,hgc,hgd,?_⟩
  have heq : U - hgi.toLp (g ∘ X) = (hi.sub hgi).toLp (f ∘ X - g ∘ X) := by
    rw [MemLp.toLp_sub hi hgi]
    congr 1
    exact Lp.ext (hUf.trans hi.coeFn_toLp.symm)
  rw [heq,Lp.norm_toLp]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hge).trans_eq (ENNReal.toReal_ofReal hε.le)

end Asakura.Chapter12

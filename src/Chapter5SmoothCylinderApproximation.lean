import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.Analysis.Calculus.FDeriv.Const
import Chapter5RepresentationClosure

open MeasureTheory Set
open scoped ContDiff ENNReal
namespace Asakura.Chapter5

/-- Smooth compactly supported approximation in the *actual law* of the
finite Brownian vector. No nondegeneracy or Lebesgue density is required. -/
theorem smooth_cylinder_approximation {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → E) (hX : Measurable X) (f : E → ℝ) (hf : Measurable f)
    (hi : MemLp (f ∘ X) 2 P) (ε : ℝ) (hε : 0 < ε) :
    ∃ g : E → ℝ, HasCompactSupport g ∧ ContDiff ℝ ∞ g ∧
      (∃ C : ℝ, ∀ x, ‖fderiv ℝ g x‖ ≤ C) ∧
      eLpNorm (fun w => f (X w)-g (X w)) 2 P ≤ ENNReal.ofReal ε := by
  have him : MemLp f 2 (P.map X) :=
    (memLp_map_measure_iff hf.aestronglyMeasurable hX.aemeasurable).2 hi
  obtain ⟨g,hgc,hgd,hge⟩ := him.exist_eLpNorm_sub_le (by norm_num) (by norm_num) hε
  have hdc : Continuous (fderiv ℝ g) := hgd.continuous_fderiv (by simp)
  have hcompact : IsCompact (range (fderiv ℝ g)) := (hgc.fderiv (𝕜 := ℝ)).isCompact_range hdc
  obtain ⟨C,hC⟩ := hcompact.exists_bound_of_continuousOn (continuous_id.continuousOn)
  refine ⟨g,hgc,hgd,⟨C,fun x => hC _ ⟨x,rfl⟩⟩,?_⟩
  have he := eLpNorm_map_measure ((hf.sub hgd.continuous.measurable).aestronglyMeasurable (μ := P.map X)) hX.aemeasurable (p := 2)
  rw [he] at hge
  exact hge

end Asakura.Chapter5

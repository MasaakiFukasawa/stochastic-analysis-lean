import Chapter10IntegratingFactorRegularity

open MeasureTheory Set
namespace Asakura.Chapter10
open Asakura.Chapter6

/-- Any continuous preterminal coefficient can be extended from a fixed
compact interval, without altering its values or integrating factor there. -/
theorem compact_coefficient_extension (f : ℝ → ℝ) (R : ℝ) (hR : 0≤R)
    (hf : ContinuousOn f (Icc 0 R)) :
    ∃ g : ℝ → ℝ,Continuous g ∧ (∀ t∈Icc 0 R,g t=f t) ∧
      ∀ t∈Icc 0 R,linearIntegratingFactor g t=linearIntegratingFactor f t := by
  let g := fun t => f (projIcc 0 R hR t)
  have hg : Continuous g := hf.comp_continuous
    (continuous_subtype_val.comp continuous_projIcc) (fun t => (projIcc 0 R hR t).property)
  have he t (ht : t∈Icc 0 R) : g t=f t := by
    dsimp only [g]; rw [projIcc_of_mem hR ht]
  refine ⟨g,hg,he,?_⟩
  intro t ht
  unfold linearIntegratingFactor
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le ht.1] at hs
  exact he s ⟨hs.1,hs.2.trans ht.2⟩

end Asakura.Chapter10

import Chapter5BackwardHeatGenerator

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal BigOperators
namespace Asakura.Chapter5
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false

/-- A globally C² function with zero backwards generator is constructed
from the actual Gaussian integral, including degenerate noise directions. -/
theorem backward_gaussian_zero_generator
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (n : ℕ) (Q : (Fin (n+1) → ℝ) →L[ℝ] E)
    (f : E → ℝ) (D : E → E →L[ℝ] ℝ) (DD : E → E →L[ℝ] E →L[ℝ] ℝ)
    (hd : ∀ x,HasFDerivAt f (D x) x) (hdd : ∀ x,HasFDerivAt D (DD x) x)
    (hDc : Continuous D) (hDDc : Continuous DD)
    (C K : ℝ≥0) (hD : ∀ x,‖D x‖≤C) (hDD : ∀ x,‖DD x‖≤K)
    (b S : ℝ) (hb : b<S) :
    let ν := (Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1)).map Q
    ∃ g : E × ℝ → ℝ,ContDiff ℝ 2 g ∧
      (∀ p : E × ℝ,p.2≤b → g p=∫ z,f (p.1+Real.sqrt (S-p.2) • z) ∂ν) ∧
      (∀ p : E × ℝ,p.2≤b →
        fderiv ℝ g p (0,1)+(1/2:ℝ)*∑ i,
          fderiv ℝ (fderiv ℝ g) p (Q (Pi.single i 1),0) (Q (Pi.single i 1),0)=0) := by
  dsimp only
  let μ := Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1)
  let ν := μ.map Q
  have hi : MemLp (fun z : E => z) 2 ν := linear_image_second_moment μ Q
    (Asakura.FullAudit.finite_gaussian_all_moments 2 (by norm_num))
  obtain ⟨g,hg,he⟩ := backward_heat_C2_extension ν hi f D DD hd hdd hDc hDDc C K hD hDD b S hb
  refine ⟨g,hg,(fun p hp => (he p hp).eq_of_nhds),?_⟩
  apply backward_heat_extension_generator Q
    (fun t x => ∫ z,f (x+Real.sqrt t • z) ∂ν) g hg b S hb he
  intro x t ht
  exact gaussian_subspace_heat_equation n Q f D DD hd hdd hDc hDDc C K hD hDD x t ht

end Asakura.Chapter5

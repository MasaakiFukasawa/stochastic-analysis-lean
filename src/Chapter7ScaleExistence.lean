import Chapter7ScaleWeakSolutionCommon
import BrownianExists

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter4

/-- Existence of a probability space and weak solution: no Brownian driver
is required as an additional input to the scale-function result. -/
theorem scale_weak_solution_exists
    (μ σ : ℝ → ℝ) (hμ : Continuous μ) (hσ : Continuous σ)
    (hσp : ∀ x,0 < σ x) (x0 : ℝ)
    (hsur : Function.Surjective (scaleFunction μ σ x0)) :
    ∃ (Ω : Type) (m : MeasurableSpace Ω) (P : Measure Ω) (hP : IsProbabilityMeasure P),
    letI := m
    letI := hP
    ∃ W : BrownianSystem P 1,∃ X Z : HalfClosedTime → Ω → ℝ,
      (∀ t,t < ⊤ → Measurable[W.F t] (X t)) ∧
      (∀ w t,t < ⊤ → ContinuousAt (fun s => X s w) t) ∧
      LocalMProcessWitness P W.F Z ∧
      ItoCovarianceFormula P W.F (W.W 0) (fun z => σ (X (realTimeClamp z.2) z.1)) Z ∧
      ∀ᵐ w ∂P,∀ r : ℝ,0 ≤ r → X (realTimeClamp r) w = x0+(∫ s in 0..r,μ (X (realTimeClamp s) w))+Z (realTimeClamp r) w := by
  obtain ⟨Ω,m,P,hP,B,hm,hc,hB,_⟩ := Asakura.brownian_motion_exists
  letI := m
  letI := hP
  exact ⟨Ω,m,P,hP,scale_weak_solution_common_written P B hB.toIsPreBrownianReal hm hc μ σ hμ hσ hσp x0 hsur⟩

end Asakura.Chapter7

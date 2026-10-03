import Chapter7ScaleWeakSolution
import Chapter7SDECommonTime

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter4

theorem scale_weak_solution_common_written
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (hB : IsPreBrownianReal B P)
    (hm : ∀ t,Measurable (B t)) (hc : ∀ w,Continuous (fun t => B t w))
    (μ σ : ℝ → ℝ) (hμ : Continuous μ) (hσ : Continuous σ)
    (hσp : ∀ x,0 < σ x) (x0 : ℝ)
    (hsur : Function.Surjective (scaleFunction μ σ x0)) :
    ∃ W : BrownianSystem P 1,∃ X Z : HalfClosedTime → Ω → ℝ,
      (∀ t,t < ⊤ → Measurable[W.F t] (X t)) ∧
      (∀ w t,t < ⊤ → ContinuousAt (fun s => X s w) t) ∧
      LocalMProcessWitness P W.F Z ∧
      ItoCovarianceFormula P W.F (W.W 0) (fun z => σ (X (realTimeClamp z.2) z.1)) Z ∧
      ∀ᵐ w ∂P,∀ r : ℝ,0 ≤ r → X (realTimeClamp r) w = x0+(∫ s in 0..r,μ (X (realTimeClamp s) w))+Z (realTimeClamp r) w := by
  obtain ⟨W,X,Z,hXa,hXc,hZ,hZI,he⟩ := scale_weak_solution_written P B hB hm hc μ σ hμ hσ hσp x0 hsur
  exact ⟨W,X,Z,hXa,hXc,hZ,hZI,sde_identity_common_time P X Z x0 μ hμ hXc (hZ.path P W.F) he⟩

end Asakura.Chapter7

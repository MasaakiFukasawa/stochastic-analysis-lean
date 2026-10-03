import Chapter7ScaleC2
import Chapter7AutonomousWeakSolution
import Chapter7ScalarDiffusionTransform

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false

/-- The scale-function example from its original coefficient assumptions.
The clock, the drift-free weak solution, the inverse C² map, and the new
Ito integral are all constructed. Surjectivity follows in particular
from the manuscript's bijection on its stated interval. -/
theorem scale_weak_solution_written
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
      ∀ r : ℝ,0 ≤ r → X (realTimeClamp r) =ᵐ[P]
        fun w => x0+(∫ s in 0..r,μ (X (realTimeClamp s) w))+Z (realTimeClamp r) w := by
  obtain ⟨_,g,hgc,hsg,hgs,hgd,hgdd,hsc,hsp⟩ := scale_c2_and_inverse μ σ hμ hσ hσp x0 hsur
  let sc := fun y => scaleDensity μ σ x0 (g y)*σ (g y)
  obtain ⟨W,Y,hY,hYI⟩ := autonomous_weak_solution_written P B hB hm hc sc hsc (fun y => ne_of_gt (hsp y))
  obtain ⟨Z,hZ,hZI,he⟩ := scalar_diffusion_transform P W Y hY sc hsc hYI g (deriv g) (deriv (deriv g)) hgc
    (fun y => ((hgc.differentiable (by norm_num)) y).hasDerivAt)
    (fun y => (hgc.differentiable_deriv_two y).hasDerivAt)
  let X := fun t w => g (Y t w)
  have hp y : scaleDensity μ σ x0 (g y) ≠ 0 := ne_of_gt (Real.exp_pos _)
  have hc1 y : deriv g y*sc y = σ (g y) := by
    rw [hgd]
    exact (inverse_scale_coefficients _ _ (μ (g y)) (hp y) (ne_of_gt (hσp (g y)))).1
  have hc2 y : deriv (deriv g) y*(sc y)^2/2 = μ (g y) := by
    rw [hgdd]
    exact (inverse_scale_coefficients _ _ (μ (g y)) (hp y) (ne_of_gt (hσp (g y)))).2
  have hg0 : g 0 = x0 := by simpa only [scaleFunction,intervalIntegral.integral_same] using hgs x0
  refine ⟨W,X,Z,fun t ht => hgc.continuous.measurable.comp (hY.adapted P W.F t ht),
    fun w t ht => hgc.continuous.continuousAt.comp (hY.path P W.F w t ht),hZ,?_,?_⟩
  · apply ito_integrand_common_ae P W.F (W.W 0) Z _ _ hZI
    exact ae_of_all _ fun w r => hc1 _
  · intro r hr
    filter_upwards [he r hr] with w hw
    have hid : (∫ s in 0..r,deriv (deriv g) (Y (realTimeClamp s) w)*(sc (Y (realTimeClamp s) w))^2)/2 =
        ∫ s in 0..r,μ (X (realTimeClamp s) w) := by
      rw [← intervalIntegral.integral_div]
      apply intervalIntegral.integral_congr
      intro s _
      exact hc2 _
    rw [hg0,hid] at hw
    change g (Y (realTimeClamp r) w) = _
    linarith

end Asakura.Chapter7

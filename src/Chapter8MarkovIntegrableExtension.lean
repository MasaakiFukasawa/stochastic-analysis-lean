import Chapter4SmoothMeasureDetermination
import Chapter8IntegrableMarkov
import Mathlib.Probability.Kernel.MeasurableIntegral

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter8
open Asakura.Chapter4
set_option maxHeartbeats 3600000
set_option backward.isDefEq.respectTransparency false

/-- Extend the actual bounded Markov identity to every integrable observable,
using restricted laws and conditional integration. -/
theorem markov_integrable_of_bounded
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {dim : ℕ} (G : MeasurableSpace Ω) (hG : G≤m)
    (X Y : Ω → (Fin dim → ℝ)) (hX : Measurable[G] X) (hY : Measurable[m] Y)
    (μ : (Fin dim → ℝ) → Measure (Fin dim → ℝ)) [∀ x,IsProbabilityMeasure (μ x)]
    (hμ : Measurable μ)
    (he : ∀ f : (Fin dim → ℝ) → ℝ,Measurable f → ∀ C : ℝ,(∀ x,‖f x‖≤C) →
      P[(fun w => f (Y w)) | G]=ᵐ[P] fun w => ∫ y,f y ∂μ (X w))
    (f : (Fin dim → ℝ) → ℝ) (hf : Measurable f) (hi : Integrable f (@Measure.map Ω _ m _ Y P)) :
    P[(fun w => f (Y w)) | G]=ᵐ[P] fun w => ∫ y,f y ∂μ (X w) := by
  letI : MeasurableSpace Ω := m
  let κ : Kernel Ω (Fin dim → ℝ) := ⟨fun w => μ (X w),hμ.comp (hX.mono hG le_rfl)⟩
  letI : IsMarkovKernel κ := ⟨fun w => inferInstanceAs (IsProbabilityMeasure (μ (X w)))⟩
  have hlaw A (hA : MeasurableSet[G] A) : (P.restrict A).map Y=κ ∘ₘ (P.restrict A) := by
    apply measure_eq_of_smooth_compact_tests
    intro f hf hfc
    obtain ⟨C,hC⟩ := hfc.exists_bound_of_continuous hf.continuous
    have hfi : Integrable (fun w => f (Y w)) P := Integrable.of_bound
      (hf.continuous.measurable.comp hY).aestronglyMeasurable C (ae_of_all _ fun w => hC (Y w))
    have hν : Integrable f (κ ∘ₘ (P.restrict A)) :=
      Integrable.of_bound hf.continuous.aestronglyMeasurable C (ae_of_all _ hC)
    have hs := (setIntegral_condExp hG hfi hA).symm.trans
      (setIntegral_congr_ae (hG A hA) ((he f hf.continuous.measurable C hC).mono fun w hw _ => hw))
    rw [integral_map hY.aemeasurable hf.continuous.aestronglyMeasurable]
    rw [hs]
    exact (Kernel.integral_comp (κ := Kernel.const Unit (P.restrict A)) (η := κ) (a := ()) hν).symm
  have hVm : StronglyMeasurable[G] (fun w => ∫ y,f y ∂μ (X w)) := by
    letI : MeasurableSpace Ω := G
    let κG : Kernel Ω (Fin dim → ℝ) := ⟨fun w => μ (X w),hμ.comp hX⟩
    exact StronglyMeasurable.integral_kernel (κ := κG) hf.stronglyMeasurable
  exact markov_integrable_test_of_restricted_laws P hG Y hY κ hlaw f hf hi hVm.aestronglyMeasurable

end Asakura.Chapter8

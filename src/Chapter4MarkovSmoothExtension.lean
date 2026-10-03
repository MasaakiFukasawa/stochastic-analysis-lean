import Chapter4SmoothMeasureDetermination
import Mathlib.Probability.Kernel.MeasurableIntegral

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter4
set_option maxHeartbeats 3600000
set_option backward.isDefEq.respectTransparency false

/-- The full Borel Markov identity follows from the smooth compact test
identities. Measurability of the transition family is derived in the proof. -/
theorem markov_borel_of_smooth_compact_tests
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {dim : ℕ} (G : MeasurableSpace Ω) (hG : G≤m)
    (X Y : Ω → (Fin dim → ℝ)) (hX : Measurable[G] X) (hY : Measurable[m] Y)
    (μ : (Fin dim → ℝ) → Measure (Fin dim → ℝ)) [∀ x,IsProbabilityMeasure (μ x)]
    (hm : ∀ f : (Fin dim → ℝ) → ℝ,ContDiff ℝ (⊤:ℕ∞) f → HasCompactSupport f →
      Measurable (fun x => ∫ y,f y ∂μ x))
    (he : ∀ f : (Fin dim → ℝ) → ℝ,ContDiff ℝ (⊤:ℕ∞) f → HasCompactSupport f →
      P[(fun w => f (Y w)) | G]=ᵐ[P] fun w => ∫ y,f y ∂μ (X w)) :
    Measurable μ ∧ ∀ f : (Fin dim → ℝ) → ℝ,Measurable f →
      ∀ C : ℝ,(∀ x,‖f x‖≤C) →
      P[(fun w => f (Y w)) | G]=ᵐ[P] fun w => ∫ y,f y ∂μ (X w) := by
  letI : MeasurableSpace Ω := m
  have hμ := transition_measure_measurable_of_smooth_tests μ hm
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
      (setIntegral_congr_ae (hG A hA) ((he f hf hfc).mono fun w hw _ => hw))
    rw [integral_map hY.aemeasurable hf.continuous.aestronglyMeasurable]
    rw [hs]
    exact (Kernel.integral_comp (κ := Kernel.const Unit (P.restrict A)) (η := κ) (a := ()) hν).symm
  refine ⟨hμ,?_⟩
  intro f hf C hC
  have hVm : StronglyMeasurable[G] (fun w => ∫ y,f y ∂μ (X w)) := by
    letI : MeasurableSpace Ω := G
    let κG : Kernel Ω (Fin dim → ℝ) := ⟨fun w => μ (X w),hμ.comp hX⟩
    exact StronglyMeasurable.integral_kernel (κ := κG) hf.stronglyMeasurable
  have hVb w : ‖∫ y,f y ∂μ (X w)‖≤C := by
    simpa only [probReal_univ,mul_one] using norm_integral_le_of_norm_le_const
      (μ := μ (X w)) (ae_of_all _ hC)
  have hVi : Integrable (fun w => ∫ y,f y ∂μ (X w)) P :=
    Integrable.of_bound (hVm.mono hG).aestronglyMeasurable C (ae_of_all _ hVb)
  have hfi : Integrable (fun w => f (Y w)) P :=
    Integrable.of_bound (hf.comp hY).aestronglyMeasurable C (ae_of_all _ fun w => hC (Y w))
  apply Filter.EventuallyEq.symm
  apply ae_eq_condExp_of_forall_setIntegral_eq hG hfi
    (fun _ _ _ => hVi.integrableOn) _ hVm.aestronglyMeasurable
  intro A hA _
  exact (markov_bounded_test_of_restricted_law P Y hY κ A (hlaw A hA) f hf C hC).symm

end Asakura.Chapter4

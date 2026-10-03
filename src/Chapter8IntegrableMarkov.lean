import Chapter4MarkovBorelExtension
import Chapter8MarkovCovariance

open MeasureTheory ProbabilityTheory Set
namespace Asakura.Chapter8

/-- The Markov identity extends from bounded tests to integrable tests by
integrating the already established restricted transition laws. This is
needed for the unbounded Lipschitz observable in the time-average theorem. -/
theorem markov_integrable_test_of_restricted_laws {Ω E : Type*}
    {G m : MeasurableSpace Ω} [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P] (hG : G ≤ m)
    (X : Ω → E) (hX : Measurable X) (κ : Kernel Ω E) [IsMarkovKernel κ]
    (hlaw : ∀ A : Set Ω, MeasurableSet[G] A →
      (P.restrict A).map X = κ ∘ₘ (P.restrict A))
    (f : E → ℝ) (hf : Measurable f) (hi : Integrable f (P.map X))
    (hg : AEStronglyMeasurable[G] (fun ω => ∫ x,f x ∂κ ω) P) :
    P[(fun ω => f (X ω))|G] =ᵐ[P] fun ω => ∫ x,f x ∂κ ω := by
  have hXi : Integrable (fun ω => f (X ω)) P := hi.comp_aemeasurable hX.aemeasurable
  have hiA (A : Set Ω) (hA : MeasurableSet[G] A) :
      Integrable f (κ ∘ₘ (P.restrict A)) := by
    rw [← hlaw A hA]
    exact (integrable_map_measure hf.aestronglyMeasurable hX.aemeasurable).mpr hXi.integrableOn
  have hi0 : Integrable f (κ ∘ₘ P) := by
    simpa only [Measure.restrict_univ] using hiA univ MeasurableSet.univ
  have hki : Integrable (fun ω => ∫ x,f x ∂κ ω) P := by
    have hh : Integrable f ((κ ∘ₖ Kernel.const Unit P) ()) := by
      simpa only [Kernel.comp_apply,Kernel.const_apply] using hi0
    exact hh.integral_comp
  apply Filter.EventuallyEq.symm
  apply ae_eq_condExp_of_forall_setIntegral_eq hG hXi
    (fun A _ _ => hki.integrableOn) _ hg
  intro A hA _
  rw [← integral_map hX.aemeasurable hf.aestronglyMeasurable,hlaw A hA]
  exact (Kernel.integral_comp (κ := Kernel.const Unit (P.restrict A))
    (η := κ) (a := ()) (hiA A hA)).symm

end Asakura.Chapter8

import Chapter10CompletedFilterIdentification
import Chapter9IndependentTransition

open MeasureTheory ProbabilityTheory Set
namespace Asakura.Chapter10
open Asakura.Chapter9
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

/-- Identify the conditional distribution of the state itself, not just its
residual: it is the translate by the measurable estimate of the error law.
Applied to the proved centered Gaussian error this is N(m,S), including
singular S. -/
theorem completed_state_conditional_law {Ω U V : Type*} [mΩ : MeasurableSpace Ω]
    [MeasurableSpace U] [MeasurableSpace V]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ}
    (Y : Ω → U) (I : Ω → V) (hY : Measurable Y) (hI : Measurable I)
    (e a : Ω → Fin d → ℝ) (he : Measurable e) (hind : IndepFun e I P)
    (hinfo : nullAugmentedInformation (m := mΩ) P (MeasurableSpace.comap Y inferInstance)=
      nullAugmentedInformation (m := mΩ) P (MeasurableSpace.comap I inferInstance))
    (ha : Measurable[nullAugmentedInformation (m := mΩ) P (MeasurableSpace.comap Y inferInstance)] a)
    (f : (Fin d → ℝ) → ℝ) (hf : Measurable f) (C : ℝ) (hbound : ∀ x,‖f x‖≤C) :
    P[(fun w => f (a w+e w))|
      nullAugmentedInformation (m := mΩ) P (MeasurableSpace.comap Y inferInstance)]=ᵐ[P]
      fun w => ∫ z,f (a w+z) ∂P.map e := by
  letI : MeasurableSpace Ω := mΩ
  let H := nullAugmentedInformation (m := mΩ) P (MeasurableSpace.comap Y inferInstance)
  letI : MeasurableSpace Ω := mΩ
  have hH : H≤mΩ := null_augmented_le P _ hY.comap_le
  have hInd : Indep (MeasurableSpace.comap e inferInstance) H P := by
    dsimp only [H]
    rw [hinfo]
    exact independent_completed_history P _ _ he.comap_le hI.comap_le hind
  letI : IsProbabilityMeasure (P.map e) := (Measure.isProbabilityMeasure_map_iff he.aemeasurable).mpr inferInstance
  exact independent_noise_borel_transition P H hH e he (P.map e) (hasLaw_map he.aemeasurable)
    hInd a ha (fun z => z.1+z.2) (measurable_fst.add measurable_snd)
    (fun z => continuous_id.add continuous_const) f hf C hbound

end Asakura.Chapter10

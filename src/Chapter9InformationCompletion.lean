import Chapter9ConditionalPiSystem

open MeasureTheory Set
namespace Asakura.Chapter9
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

/-- Adjoin the ambient measurable null events to a sigma algebra. -/
def nullAugmentedInformation {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) (G : MeasurableSpace Ω) : MeasurableSpace Ω :=
  MeasurableSpace.generateFrom {A : Set Ω | MeasurableSet[G] A ∨ (MeasurableSet[m] A ∧ P A=0)}

theorem null_augmented_contains {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) (G : MeasurableSpace Ω) : G≤nullAugmentedInformation (m := m) P G := by
  intro A hA
  exact MeasurableSpace.measurableSet_generateFrom (Or.inl hA)

theorem null_augmented_le {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) (G : MeasurableSpace Ω) (hG : G≤m) : nullAugmentedInformation (m := m) P G≤m := by
  apply MeasurableSpace.generateFrom_le
  intro A hA
  exact hA.elim (hG A) And.left

/-- Adding null events changes every measurable event only by a null set. -/
theorem null_augmented_event {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) (G : MeasurableSpace Ω) (A : Set Ω)
    (hA : MeasurableSet[nullAugmentedInformation (m := m) P G] A) :
    ∃ B : Set Ω,MeasurableSet[G] B ∧ A =ᵐ[P] B := by
  induction A,hA using MeasurableSpace.generateFrom_induction with
  | hC A hA _ =>
    rcases hA with hA|⟨hm,hnull⟩
    · exact ⟨A,hA,Filter.EventuallyEq.rfl⟩
    · refine ⟨∅,MeasurableSet.empty,?_⟩
      apply ae_iff.mpr
      simpa using hnull
  | empty => exact ⟨∅,MeasurableSet.empty,Filter.EventuallyEq.rfl⟩
  | compl A _ ih =>
    obtain ⟨B,hB,he⟩ := ih
    exact ⟨Bᶜ,hB.compl,he.mono (fun w hw => congrArg Not hw)⟩
  | iUnion A hA ih =>
    choose B hB he using ih
    refine ⟨⋃ n,B n,MeasurableSet.iUnion hB,?_⟩
    filter_upwards [ae_all_iff.mpr he] with w hw
    simp only [Set.mem_iUnion]
    exact propext (exists_congr (fun n => (hw n).to_iff))

/-- Conditional expectations are unchanged by adjoining null events. -/
theorem conditional_expectation_null_augmentation {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (G : MeasurableSpace Ω) (hG : G≤m)
    (Y Z : Ω → ℝ) (hY : Integrable Y P) (hZ : AEStronglyMeasurable[G] Z P)
    (he : P[Y|G]=ᵐ[P] Z) : P[Y|nullAugmentedInformation (m := m) P G]=ᵐ[P] Z := by
  letI : MeasurableSpace Ω := m
  have hi : Integrable Z P := integrable_condExp.congr he
  apply (ae_eq_condExp_of_forall_setIntegral_eq (null_augmented_le (m := m) P G hG) hY
    (fun A _ _ => hi.integrableOn) ?_ (hZ.mono (null_augmented_contains (m := m) P G))).symm
  intro A hA _
  obtain ⟨B,hB,hAB⟩ := null_augmented_event (m := m) P G A hA
  rw [setIntegral_congr_set hAB,setIntegral_congr_set hAB]
  rw [←setIntegral_condExp hG hY hB]
  exact setIntegral_congr_ae (hG B hB) (he.symm.mono (fun w hw _ => hw))
end Asakura.Chapter9

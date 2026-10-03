import Chapter9ReverseFields
import Chapter9InformationCompletion

open MeasureTheory Set
namespace Asakura.Chapter9
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

noncomputable def ouReverseParamTransition {d : ℕ} (μ : Measure (Fin d → ℝ)) (T s : ℝ)
    (g : ℝ × (Fin d → ℝ) → ℝ) (z : ℝ × (Fin d → ℝ)) : ℝ :=
  (∫ y,g (z.1,y)*ouCoordinateDensity μ (T-z.1,y)*
    gaussianKernel (Real.exp (-(z.1-s))) (1-Real.exp (-2*(z.1-s))) y z.2)/
      ouCoordinateDensity μ (T-s,z.2)

theorem ou_reverse_param_transition_measurable {d : ℕ} (μ : Measure (Fin d → ℝ)) [SFinite μ]
    (T s : ℝ) (g : ℝ × (Fin d → ℝ) → ℝ) (hg : Measurable g) :
    Measurable (ouReverseParamTransition μ T s g) := by
  have hp := ou_coordinate_density_measurable μ
  have hm : Measurable (fun z : (ℝ × (Fin d → ℝ)) × (Fin d → ℝ) =>
      g (z.1.1,z.2)*ouCoordinateDensity μ (T-z.1.1,z.2)*
        gaussianKernel (Real.exp (-(z.1.1-s))) (1-Real.exp (-2*(z.1.1-s))) z.2 z.1.2) := by
    apply Measurable.mul
    · exact (hg.comp (by fun_prop)).mul (hp.comp (by fun_prop))
    · unfold gaussianKernel
      fun_prop
  exact hm.stronglyMeasurable.integral_prod_right'.measurable.div (hp.comp (by fun_prop))

def reversedNaturalInformation {Ω E : Type*} [m : MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) (X : ℝ → Ω → E) (T a : ℝ) : MeasurableSpace Ω :=
  nullAugmentedInformation (m := m) P
    (MeasurableSpace.comap (fun w (r : Icc (T-a) T) => X r w) MeasurableSpace.pi)

 theorem null_augmented_mono {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) (G H : MeasurableSpace Ω) (hGH : G≤H) :
    nullAugmentedInformation (m := m) P G≤nullAugmentedInformation (m := m) P H := by
  apply MeasurableSpace.generateFrom_mono
  intro A hA
  exact hA.elim (fun h => Or.inl (hGH A h)) Or.inr

theorem reversed_information_monotone {Ω E : Type*} [m : MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) (X : ℝ → Ω → E) (T : ℝ) : Monotone (reversedNaturalInformation P X T) := by
  intro a b hab
  apply null_augmented_mono (m := m) P
  let H := MeasurableSpace.comap (fun w (r : Icc (T-b) T) => X r w) MeasurableSpace.pi
  letI : MeasurableSpace Ω := H
  have hh : Measurable[H] (fun w (r : Icc (T-a) T) => X r w) := by
    apply Measurable.of_eval
    intro r
    exact (measurable_pi_apply (⟨r.val,(sub_le_sub_left hab T).trans r.property.1,r.property.2⟩ : Icc (T-b) T)).comp
      (comap_measurable (fun w (r : Icc (T-b) T) => X r w))
  exact hh.comap_le

theorem reversed_information_le {Ω E : Type*} [m : MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) (X : ℝ → Ω → E) (hX : ∀ t,Measurable (X t)) (T a : ℝ) :
    reversedNaturalInformation P X T a≤m := by
  apply null_augmented_le (m := m) P
  exact (measurable_pi_iff.mpr (fun r : Icc (T-a) T => hX r)).comap_le

theorem reversed_state_adapted {Ω E : Type*} [m : MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) (X : ℝ → Ω → E) (T a : ℝ) (ha : 0≤a) :
    Measurable[reversedNaturalInformation P X T a] (X (T-a)) := by
  have hm : Measurable[MeasurableSpace.comap (fun w (r : Icc (T-a) T) => X r w) MeasurableSpace.pi]
      (X (T-a)) := (measurable_pi_apply (⟨T-a,le_rfl,by linarith⟩ : Icc (T-a) T)).comp
        (comap_measurable (fun w (r : Icc (T-a) T) => X r w))
  exact hm.mono (null_augmented_contains (m := m) P _) le_rfl

theorem reversed_information_null {Ω E : Type*} [m : MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) (X : ℝ → Ω → E) (T a : ℝ) (N : Set Ω)
    (hN : MeasurableSet[m] N) (hPN : P N=0) : MeasurableSet[reversedNaturalInformation P X T a] N :=
  MeasurableSpace.measurableSet_generateFrom (Or.inr ⟨hN,hPN⟩)
end Asakura.Chapter9

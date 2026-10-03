import Chapter9BoundedTests
import Chapter9InformationCompletion

open MeasureTheory Set
namespace Asakura.Chapter9
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

/-- An identity conditioned on the entire forward future also holds for
the finite future ending at T, with the null events adjoined. -/
theorem finite_future_regression {Ω E : Type*} [m : MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ → Ω → E) (hX : ∀ t,Measurable (X t))
    (t T : ℝ) (htT : t≤T) (Y : Ω → ℝ) (hY : Integrable Y P)
    (z : E → ℝ) (hz : IsBoundedBorel z)
    (he : P[Y|MeasurableSpace.comap (fun w (r : Ici t) => X r w) MeasurableSpace.pi]=ᵐ[P]
      (fun w => z (X t w))) :
    P[Y|nullAugmentedInformation (m := m) P
      (MeasurableSpace.comap (fun w (r : Icc t T) => X r w) MeasurableSpace.pi)]=ᵐ[P]
      (fun w => z (X t w)) := by
  let H := MeasurableSpace.comap (fun w (r : Ici t) => X r w) MeasurableSpace.pi
  let G := MeasurableSpace.comap (fun w (r : Icc t T) => X r w) MeasurableSpace.pi
  letI : MeasurableSpace Ω := m
  have hH : H≤m := (measurable_pi_iff.mpr (fun r : Ici t => hX r)).comap_le
  have hG : G≤m := (measurable_pi_iff.mpr (fun r : Icc t T => hX r)).comap_le
  have hGH : G≤H := by
    letI : MeasurableSpace Ω := H
    have hh : Measurable[H] (fun w (r : Icc t T) => X r w) := by
      apply Measurable.of_eval
      intro r
      exact (measurable_pi_apply (⟨r.val,r.property.1⟩ : Ici t)).comp
        (comap_measurable (fun w (r : Ici t) => X r w))
    exact hh.comap_le
  have hm : Measurable[G] (fun w => z (X t w)) :=
    hz.1.comp ((measurable_pi_apply (⟨t,le_rfl,htT⟩ : Icc t T)).comp
      (comap_measurable (fun w (r : Icc t T) => X r w)))
  have hi : Integrable (fun w => z (X t w)) P := (hz.comp _ (hX t)).integrable P
  have hsmall : P[Y|G]=ᵐ[P] (fun w => z (X t w)) := by
    have hh := (condExp_condExp_of_le (μ := P) (f := Y) hGH hH).symm.trans (condExp_congr_ae (m := G) he)
    rw [condExp_of_stronglyMeasurable hG hm.stronglyMeasurable hi] at hh
    exact hh
  exact conditional_expectation_null_augmentation (m := m) P G hG Y _ hY hm.aestronglyMeasurable hsmall
end Asakura.Chapter9

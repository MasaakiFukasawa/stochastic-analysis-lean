import Chapter10GaussianHistory

open MeasureTheory ProbabilityTheory Set
namespace Asakura.Chapter10
set_option backward.isDefEq.respectTransparency false

/-- Independence of the vector error determines each conditional second moment.
The conditioning sigma algebra is the full observation history. -/
theorem independent_error_conditional_covariance {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (G : MeasurableSpace Ω) (hG : G ≤ m)
    {d : ℕ} (e : Ω → Fin d → ℝ) (he : Measurable[m] e)
    (hind : Indep (MeasurableSpace.comap e inferInstance) G P) (i j : Fin d) :
    P[(fun w => e w i * e w j) | G] =ᵐ[P]
      (fun _ => ∫ w, e w i * e w j ∂P) := by
  letI : MeasurableSpace Ω := m
  have hm : Measurable[MeasurableSpace.comap e inferInstance] e :=
    Measurable.of_comap_le le_rfl
  exact condExp_indep_eq he.comap_le hG
    (((measurable_pi_apply i).comp hm).mul ((measurable_pi_apply j).comp hm)).stronglyMeasurable hind

/-- Bounded Borel tests of an independent error have constant conditional means;
this identifies its conditional distribution, including singular Gaussian laws. -/
theorem independent_error_conditional_test {Ω E : Type*} {m : MeasurableSpace Ω}
    [MeasurableSpace E] (P : Measure Ω) [IsProbabilityMeasure P]
    (G : MeasurableSpace Ω) (hG : G ≤ m) (e : Ω → E) (he : Measurable[m] e)
    (hind : Indep (MeasurableSpace.comap e inferInstance) G P)
    (f : E → ℝ) (hf : Measurable f) :
    P[(f ∘ e) | G] =ᵐ[P] (fun _ => ∫ w, f (e w) ∂P) := by
  letI : MeasurableSpace Ω := m
  exact condExp_indep_eq he.comap_le hG
    (hf.comp (Measurable.of_comap_le le_rfl)).stronglyMeasurable hind

end Asakura.Chapter10

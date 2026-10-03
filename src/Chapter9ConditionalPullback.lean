import Chapter9BoundedTests

open MeasureTheory Set
namespace Asakura.Chapter9
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

/-- A regression computed under a joint law pulls back to any random
variables having that joint law, without assuming a conditional-density formula. -/
theorem bounded_regression_pullback {Ω A : Type*} [mΩ : MeasurableSpace Ω] [mA : MeasurableSpace A]
    (P : Measure Ω) [IsProbabilityMeasure P] (Q : Measure A) [IsProbabilityMeasure Q]
    (X : Ω → A) (hX : Measurable X) (hlaw : P.map X=Q)
    (G : MeasurableSpace A) (hG : G≤mA) (f g : A → ℝ)
    (hf : @IsBoundedBorel A mA f) (hg : @IsBoundedBorel A mA g) (hgG : Measurable[G] g)
    (he : Q[f|G]=ᵐ[Q] g) :
    P[(fun w => f (X w))|MeasurableSpace.comap X G]=ᵐ[P] (fun w => g (X w)) := by
  letI : MeasurableSpace A := mA
  letI : MeasurableSpace Ω := mΩ
  have hle : MeasurableSpace.comap X G≤mΩ := (MeasurableSpace.comap_mono hG).trans hX.comap_le
  have hfi := (hf.comp X hX).integrable P
  have hgi := (hg.comp X hX).integrable P
  have hm : Measurable[MeasurableSpace.comap X G] (fun w => g (X w)) :=
    hgG.comp (comap_measurable X)
  apply (ae_eq_condExp_of_forall_setIntegral_eq hle hfi
    (fun S _ _ => hgi.integrableOn) ?_ hm.aestronglyMeasurable).symm
  rintro S ⟨B,hB,rfl⟩ _
  have hfmap := setIntegral_map (μ := P) (hG B hB) hf.1.aestronglyMeasurable hX.aemeasurable
  have hgmap := setIntegral_map (μ := P) (hG B hB) hg.1.aestronglyMeasurable hX.aemeasurable
  rw [hlaw] at hfmap hgmap
  rw [←hgmap,←hfmap,←setIntegral_condExp hG (hf.integrable Q) hB]
  exact setIntegral_congr_ae (hG B hB) (he.symm.mono (fun a ha _ => ha))
end Asakura.Chapter9

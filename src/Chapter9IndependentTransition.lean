import Chapter4IndependentNoiseParameter
import Chapter4MarkovSmoothExtension

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace Asakura.Chapter9
open Asakura.Chapter4
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

/-- An independent noise input gives the full bounded Borel conditional
transition formula, including arbitrary measurable current states. -/
theorem independent_noise_borel_transition {Ω D : Type*} {m : MeasurableSpace Ω}
    [MeasurableSpace D] {d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (G : MeasurableSpace Ω) (hG : G≤m)
    (Z : Ω → D) (hZ : Measurable[m] Z) (ν : Measure D) [IsProbabilityMeasure ν]
    (hlaw : HasLaw Z ν P) (hind : Indep (MeasurableSpace.comap Z inferInstance) G P)
    (η : Ω → Fin d → ℝ) (hη : Measurable[G] η)
    (F : (Fin d → ℝ) × D → (Fin d → ℝ)) (hF : Measurable F)
    (hc : ∀ z,Continuous (fun x => F (x,z))) :
    ∀ f : (Fin d → ℝ) → ℝ,Measurable f → ∀ C : ℝ,(∀ x,‖f x‖≤C) →
      P[(fun w => f (F (η w,Z w))) | G]=ᵐ[P]
        fun w => ∫ z,f (F (η w,z)) ∂ν := by
  letI : MeasurableSpace Ω := m
  let μ := fun x : Fin d → ℝ => ν.map (fun z => F (x,z))
  have hFm x : Measurable (fun z => F (x,z)) := hF.comp (measurable_const.prodMk measurable_id)
  letI (x : Fin d → ℝ) : IsProbabilityMeasure (μ x) :=
    (Measure.isProbabilityMeasure_map_iff (hFm x).aemeasurable).mpr inferInstance
  have he (x : Fin d → ℝ) (f : (Fin d → ℝ) → ℝ) (hf : Measurable f) :
      (∫ y,f y ∂μ x)=∫ z,f (F (x,z)) ∂ν := integral_map (hFm x).aemeasurable hf.aestronglyMeasurable
  have hY : Measurable[m] (fun w => F (η w,Z w)) := hF.comp ((hη.mono hG le_rfl).prodMk hZ)
  have hm (f : (Fin d → ℝ) → ℝ) (hf : ContDiff ℝ (⊤:ℕ∞) f) (hfc : HasCompactSupport f) :
      Measurable (fun x => ∫ y,f y ∂μ x) := by
    obtain ⟨C,hC⟩ := hfc.exists_bound_of_continuous hf.continuous
    have hh := (bounded_parameter_integral ν (fun z => f (F z)) (hf.continuous.measurable.comp hF)
      C (fun x z => hC _)).1
    simpa only [he _ f hf.continuous.measurable] using hh
  have ht (f : (Fin d → ℝ) → ℝ) (hf : ContDiff ℝ (⊤:ℕ∞) f) (hfc : HasCompactSupport f) :
      P[(fun w => f (F (η w,Z w))) | G]=ᵐ[P] fun w => ∫ y,f y ∂μ (η w) := by
    obtain ⟨C,hC⟩ := hfc.exists_bound_of_continuous hf.continuous
    have hh := independent_noise_parameter_condExp P G hG Z hZ ν hlaw hind η hη
      (fun z => f (F z)) (hf.continuous.measurable.comp hF)
      (fun z => hf.continuous.comp (hc z)) C (fun x z => hC _)
    simpa only [he _ f hf.continuous.measurable] using hh
  have hh := (markov_borel_of_smooth_compact_tests P G hG η (fun w => F (η w,Z w)) hη hY μ hm ht).2
  intro f hf C hC
  simpa only [he _ f hf] using hh f hf C hC
end Asakura.Chapter9

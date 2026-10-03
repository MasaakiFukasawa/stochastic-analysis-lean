import FullAuditNaturalFiltration
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

open MeasureTheory Set
namespace Asakura.Chapter12
open Asakura.FullAudit
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/-- Adding ambient null sets introduces no new real random variables up to
a.e. equality. The arctangent makes the conditional-expectation argument
applicable even when the original measurable variable is not integrable. -/
theorem null_augmentation_aestronglyMeasurable {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (G : MeasurableSpace Ω) (hG : G≤m)
    (f : Ω → ℝ) (hf : Measurable[Asakura.nullAugmentation (m := m) P G] f) :
    AEStronglyMeasurable[G] f P := by
  letI : MeasurableSpace Ω := m
  let A := Asakura.nullAugmentation (m := m) P G
  have hA : A≤m := fun s hs => hs.1
  have hfm : Measurable[A] (fun w => Real.arctan (f w)) := Real.continuous_arctan.measurable.comp hf
  have hi : Integrable (fun w => Real.arctan (f w)) P := by
    apply Integrable.of_bound ((hfm.mono hA le_rfl).stronglyMeasurable.aestronglyMeasurable) (Real.pi/2)
    exact ae_of_all _ fun w => by
      rw [Real.norm_eq_abs]
      exact (abs_lt.mpr ⟨Real.neg_pi_div_two_lt_arctan _,Real.arctan_lt_pi_div_two _⟩).le
  have he := conditional_null_augmentation P G hG _ hi
  rw [condExp_of_stronglyMeasurable hA hfm.stronglyMeasurable hi] at he
  have harg : AEStronglyMeasurable[G] (fun w => Real.arctan (f w)) P :=
    stronglyMeasurable_condExp.aestronglyMeasurable.congr he
  obtain ⟨g,hgm,hge⟩ := harg
  have htan : Measurable (Real.tan : ℝ → ℝ) := by
    convert Real.continuous_sin.measurable.div Real.continuous_cos.measurable using 1
    funext x
    exact Real.tan_eq_sin_div_cos x
  refine ⟨(fun w => Real.tan (g w)),(htan.comp hgm.measurable).stronglyMeasurable,?_⟩
  filter_upwards [hge] with w hw
  rw [← hw,Real.tan_arctan]

end Asakura.Chapter12

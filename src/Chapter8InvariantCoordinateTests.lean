import Chapter8LangevinInvariantManuscript
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory Set
open scoped NNReal
namespace Asakura.Chapter8
open Asakura.FullAudit Asakura.Chapter4 Asakura.Chapter3Complete
open Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

/-- Invariance of the actual solution law supplies exactly the coordinate
invariance tests used in the time-average and inference theorems. -/
theorem invariant_coordinate_tests {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (P : Measure Ω) [IsProbabilityMeasure P]
    {d : ℕ} (e : (Fin d → ℝ) ≃L[ℝ] E)
    (π : Measure E) [IsProbabilityMeasure π]
    (F : E → Ω → E) (hF : Measurable (Function.uncurry F))
    (Z : (Fin d → ℝ) → Ω → Fin d → ℝ)
    (hrep : ∀ x,(fun w => F (e x) w)=ᵐ[P] fun w => e (Z x w))
    (hinv : flowLaw π P F=π)
    (f : (Fin d → ℝ) → ℝ) (hf : Continuous f) (hs : HasCompactSupport f) :
    (∫ x,(∫ w,f (Z x w) ∂P) ∂π.map e.symm)=∫ x,f x ∂π.map e.symm := by
  let g := fun y : E => f (e.symm y)
  have hg : Continuous g := hf.comp e.symm.continuous
  obtain ⟨C,hC⟩ := hs.exists_bound_of_continuous hf
  have hi : Integrable (fun z : E × Ω => g (F z.1 z.2)) (π.prod P) :=
    (integrable_const C).mono' (hg.measurable.comp hF).aestronglyMeasurable
      (ae_of_all _ (fun z => hC _))
  have he : (∫ y,(∫ w,g (F y w) ∂P) ∂π)=∫ y,g y ∂π := by
    rw [←integral_prod _ hi]
    have hm := integral_map (μ := π.prod P) hF.aemeasurable hg.aestronglyMeasurable
    change (∫ y,g y ∂flowLaw π P F)=(∫ z,g (F z.1 z.2) ∂π.prod P) at hm
    rw [←hm,hinv]
  have hinner : Measurable (fun y => ∫ w,g (F y w) ∂P) :=
    (show StronglyMeasurable (Function.uncurry (fun y w => g (F y w))) from
      (hg.measurable.comp hF).stronglyMeasurable).integral_prod_right.measurable
  have hZeq x : (∫ w,f (Z x w) ∂P)=∫ w,g (F (e x) w) ∂P := by
    apply integral_congr_ae
    filter_upwards [hrep x] with w hw
    simp only [g,hw,e.symm_apply_apply]
  simp_rw [hZeq]
  have hm := integral_map (μ := π) e.symm.continuous.measurable.aemeasurable
    (hinner.comp e.continuous.measurable).aestronglyMeasurable
  simp only [Function.comp_def,e.apply_symm_apply] at hm
  rw [hm,he,integral_map e.symm.continuous.measurable.aemeasurable hf.aestronglyMeasurable]
end Asakura.Chapter8

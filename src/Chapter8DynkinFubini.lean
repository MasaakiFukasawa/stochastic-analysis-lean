import Chapter8SemigroupGenerator
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory Set Filter
namespace Asakura.Chapter8

/-- An integrable uniform path bound supplies the Fubini hypothesis in
Dynkin's formula; integrability of the time integral is a conclusion. -/
theorem dynkin_fubini {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [SFinite P] (T : ℝ) (hT : 0 ≤ T)
    (R : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry R))
    (K : Ω → ℝ) (hK : Integrable K P)
    (hb : ∀ᵐ w ∂P, ∀ s ∈ Icc 0 T, ‖R w s‖ ≤ K w) :
    Integrable (fun w => ∫ s in 0..T, R w s) P ∧
    (∫ w, (∫ s in 0..T, R w s) ∂P) = ∫ s in 0..T, ∫ w, R w s ∂P := by
  let ν := volume.restrict (Ioc (0:ℝ) T)
  have hb' : ∀ᵐ z ∂P.prod ν, ‖R z.1 z.2‖ ≤ K z.1 := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hb,
      Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Ioc)] with z hz hs
    exact hz z.2 ⟨hs.1.le, hs.2⟩
  have hi : Integrable (Function.uncurry R) (P.prod ν) :=
    (hK.comp_fst ν).mono' hm.aestronglyMeasurable hb'
  constructor
  · simpa only [intervalIntegral.integral_of_le hT, Function.uncurry, ν] using hi.integral_prod_left
  · simpa only [intervalIntegral.integral_of_le hT, Function.uncurry, ν] using integral_integral_swap hi

end Asakura.Chapter8

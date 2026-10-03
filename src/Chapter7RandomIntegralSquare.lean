import Chapter2CumulativeBound
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter7
open Asakura.Chapter2Complete
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

/-- Cauchy--Schwarz followed by Fubini for an actual random parameter
integral. Used for the squared interval integrals in the bracket estimate. -/
theorem random_integral_square {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (μ : Measure ℝ) [SigmaFinite P] [IsFiniteMeasure μ]
    (H : Ω × ℝ → ℝ) (hm : Measurable H) (hH : MemLp H 2 (P.prod μ)) :
    MemLp (fun w => ∫ s,H (w,s) ∂μ) 2 P ∧
    (∫ w,(∫ s,H (w,s) ∂μ)^2 ∂P) ≤ μ.real univ*(∫ s,∫ w,H (w,s)^2 ∂P ∂μ) := by
  have hi : Integrable (fun z => H z^2) (P.prod μ) := (memLp_two_iff_integrable_sq hH.aestronglyMeasurable).mp hH
  have hmJ : AEStronglyMeasurable (fun w => ∫ s,H (w,s) ∂μ) P :=
    (show StronglyMeasurable (Function.uncurry (fun w s => H (w,s))) from hm.stronglyMeasurable).integral_prod_right.aestronglyMeasurable
  have hb : ∀ᵐ w ∂P,(∫ s,H (w,s) ∂μ)^2 ≤ μ.real univ*(∫ s,H (w,s)^2 ∂μ) := by
    filter_upwards [hi.prod_right_ae] with w hw
    have hg : MemLp (fun s => H (w,s)) 2 μ := (memLp_two_iff_integrable_sq
      (hm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable).mpr hw
    have hh := cumulative_integral_square_bound μ (fun s => H (w,s)) hg univ
    simpa only [Measure.restrict_univ,Real.norm_eq_abs,sq_abs] using hh
  have hd : Integrable (fun w => μ.real univ*(∫ s,H (w,s)^2 ∂μ)) P :=
    hi.integral_prod_left.const_mul _
  have hJ2 : Integrable (fun w => (∫ s,H (w,s) ∂μ)^2) P := by
    apply hd.mono' (hmJ.pow 2)
    simpa only [Real.norm_eq_abs,abs_sq,Pi.pow_apply] using hb
  refine ⟨(memLp_two_iff_integrable_sq hmJ).mpr hJ2,?_⟩
  calc
    _ ≤ ∫ w,μ.real univ*(∫ s,H (w,s)^2 ∂μ) ∂P := integral_mono_ae hJ2 hd hb
    _ = _ := by rw [integral_const_mul,integral_integral_swap hi]

end Asakura.Chapter7

import Chapter7RandomFieldEnergy
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter7
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

/-- Integrating deterministic conditional means. The conditional Fubini
step is proved by its defining set-integral identity. -/
theorem conditional_integral_mean {Ω S : Type*} [m : MeasurableSpace Ω] [MeasurableSpace S]
    (P : Measure Ω) [IsProbabilityMeasure P] (μ : Measure S) [SigmaFinite μ]
    (H : Ω × S → ℝ) (hi : Integrable H (P.prod μ)) (b : S → ℝ)
    (F : MeasurableSpace Ω) (hle : F ≤ m)
    (he : ∀ᵐ s ∂μ,P[(fun w => H (w,s))|F] =ᵐ[P] fun _ => b s) :
    P[(fun w => ∫ s,H (w,s) ∂μ)|F] =ᵐ[P] fun _ => ∫ s,b s ∂μ := by
  letI : MeasurableSpace Ω := m
  apply (ae_eq_condExp_of_forall_setIntegral_eq hle hi.integral_prod_left
    (fun A _ _ => (integrable_const _).integrableOn) ?_ stronglyMeasurable_const.aestronglyMeasurable).symm
  intro A hA _
  have hres : Integrable H ((P.restrict A).prod μ) :=
    hi.mono_measure (Measure.prod_mono Measure.restrict_le_self le_rfl)
  rw [integral_integral_swap (f := fun w s => H (w,s)) hres]
  have hinner : (fun s => ∫ w in A,H (w,s) ∂P) =ᵐ[μ] fun s => P.real A*b s := by
    filter_upwards [he,hi.prod_left_ae] with s hs hsi
    rw [← setIntegral_condExp hle hsi hA]
    rw [setIntegral_congr_ae (hle A hA) (hs.mono (fun w hw _ => hw))]
    simp [Measure.real,smul_eq_mul]
  rw [integral_congr_ae hinner,integral_const_mul]
  simp [Measure.real,smul_eq_mul]

end Asakura.Chapter7

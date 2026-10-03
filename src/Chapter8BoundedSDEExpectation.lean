import Chapter8BrownianForcingPath

open MeasureTheory Set
namespace Asakura.Chapter8
open Asakura.Chapter4 Asakura.Chapter3Complete Asakura.FullAudit
open Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete

theorem bounded_sde_expectation {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d n : ℕ}
    (B : BrownianSystem P n)
    (b : Fin d → (Fin d → ℝ) → ℝ) (σ : Fin d → Fin n → (Fin d → ℝ) → ℝ)
    (x : Fin d → ℝ) (X : HalfClosedTime → Ω → Fin d → ℝ)
    (hX : VectorSDESolution P B.F B.W b σ (fun _ => x) X)
    (f : (Fin d → ℝ) → ℝ) (hf : Continuous f) (K : ℝ) (hb : ∀ y,‖f y‖≤K) :
    Continuous (fun r => ∫ w,f (X (realTimeClamp r) w) ∂P) ∧
      ∀ r,‖∫ w,f (X (realTimeClamp r) w) ∂P‖≤K := by
  have hm r : Measurable (fun w => f (X (realTimeClamp r) w)) :=
    hf.measurable.comp ((hX.adapted _ (half_real_time_finite r)).mono (B.le _) le_rfl)
  constructor
  · apply continuous_of_dominated (bound := fun _ : Ω => K)
      (fun r => (hm r).aestronglyMeasurable)
      (fun r => ae_of_all _ fun w => hb _) (integrable_const K)
    apply ae_of_all
    intro w
    apply hf.comp
    apply continuous_iff_continuousAt.mpr
    intro r
    exact (hX.path w _ (half_real_time_finite r)).comp real_time_clamp_continuous.continuousAt
  · intro r
    calc
      _ ≤ ∫ w,‖f (X (realTimeClamp r) w)‖ ∂P := norm_integral_le_integral_norm _
      _ ≤ ∫ _ : Ω,K ∂P := integral_mono_of_nonneg (ae_of_all _ fun w => norm_nonneg _)
        (integrable_const K) (ae_of_all _ fun w => hb _)
      _ = K := by simp

end Asakura.Chapter8

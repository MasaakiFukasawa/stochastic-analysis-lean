import Chapter7ClockHalfTime
import Chapter2CommonTimeEquality
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open MeasureTheory Set Filter
open scoped Topology NNReal
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1800000

theorem sde_identity_common_time
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X Z : HalfClosedTime → Ω → ℝ) (x0 : ℝ) (μ : ℝ → ℝ) (hμ : Continuous μ)
    (hX : ∀ w t,t < ⊤ → ContinuousAt (fun s => X s w) t)
    (hZ : ∀ w t,t < ⊤ → ContinuousAt (fun s => Z s w) t)
    (he : ∀ r : ℝ,0 ≤ r → X (realTimeClamp r) =ᵐ[P]
      fun w => x0+(∫ s in 0..r,μ (X (realTimeClamp s) w))+Z (realTimeClamp r) w) :
    ∀ᵐ w ∂P,∀ r : ℝ,0 ≤ r → X (realTimeClamp r) w =
      x0+(∫ s in 0..r,μ (X (realTimeClamp s) w))+Z (realTimeClamp r) w := by
  have hf r : realTimeClamp (T := (⊤:EReal)) r < ⊤ :=
    lt_of_le_of_lt (real_time_clamp_mono (le_max_right 0 r)) (changed_time_finite _ (le_max_left _ _))
  have hXr w : Continuous (fun r : ℝ => X (realTimeClamp r) w) := continuous_iff_continuousAt.mpr
    fun r => (hX w _ (hf r)).comp real_time_clamp_continuous.continuousAt
  have hZr w : Continuous (fun r : ℝ => Z (realTimeClamp r) w) := continuous_iff_continuousAt.mpr
    fun r => (hZ w _ (hf r)).comp real_time_clamp_continuous.continuousAt
  have h := continuous_process_common_time_equality P
    (fun r : ℝ≥0 => X (realTimeClamp (r:ℝ)))
    (fun (r : ℝ≥0) w => x0+(∫ s in 0..(r:ℝ),μ (X (realTimeClamp s) w))+Z (realTimeClamp (r:ℝ)) w)
    (fun w => (hXr w).comp continuous_subtype_val)
    (fun w => (continuous_const.add
      ((intervalIntegral.differentiable_integral_of_continuous (hμ.comp (hXr w))).continuous.comp continuous_subtype_val)).add
      ((hZr w).comp continuous_subtype_val))
    (fun r => he r r.property)
  exact h.mono fun w hw r hr => hw ⟨r,hr⟩

end Asakura.Chapter7

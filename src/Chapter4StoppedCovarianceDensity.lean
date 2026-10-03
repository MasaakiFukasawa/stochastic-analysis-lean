import Chapter4FiniteSDESemimartingale
import Chapter4CovarianceSumsDensity

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter5
set_option backward.isDefEq.respectTransparency false

/-- Stopping an absolutely continuous covariance at a deterministic time
multiplies its density by the interval indicator. -/
theorem stopped_covariance_density
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {T : EReal} [Fact (0≤T)]
    (C : ClosedTime T → Ω → ℝ) (G : Ω × ℝ → ℝ)
    (R : ℝ) (hR : 0≤R) (b : ℝ) (hb : 0≤b)
    (he : ∀ᵐ w ∂P,∀ r∈Icc 0 b,C (realTimeClamp r) w=∫ s in 0..r,G (w,s)) :
    ∀ᵐ w ∂P,∀ r∈Icc 0 b,C (min (realTimeClamp R) (realTimeClamp r)) w=
      ∫ s in 0..r,(Iic R).indicator (fun s => G (w,s)) s := by
  filter_upwards [he] with w hw
  intro r hr
  rw [clipped_driver_integral _ R r hR hr.1]
  have hmin : min (realTimeClamp (T := T) R) (realTimeClamp r)=realTimeClamp (min r R) := by
    rcases le_total r R with h | h
    · rw [min_eq_right (real_time_clamp_mono h),min_eq_left h]
    · rw [min_eq_left (real_time_clamp_mono h),min_eq_right h]
  rw [hmin]
  exact hw (min r R) ⟨le_min hr.1 hR,(min_le_left _ _).trans hr.2⟩

end Asakura.Chapter4

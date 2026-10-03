import Chapter4BrownianSystem
import Chapter6AEClockCross
import Chapter5BSDEFiniteEnergyData

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter6
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

/-- The second displayed identity in the linear BSDE theorem: the
covariance of the solution's martingale part with W is the time integral
of its actual Ito integrand. -/
theorem linear_bsde_bracket_written {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (c : ℕ → ℝ) (hc : ∀ n,0≤c n) (hco : ∀ r,∃ n,r≤c n)
    (R : ℝ) (u : BSDEFiniteEnergyData P B.F (B.W 0) c R) :
    ∃ C,LocalCovarianceWitness P B.F u.M (B.W 0) C ∧
      ∀ b : ℝ,0≤b → C (realTimeClamp b)=ᵐ[P] fun w => ∫ r in 0..b,u.Z (w,r) := by
  have hi b (hb : 0≤b) : ∀ᵐ w ∂P,IntervalIntegrable (fun r => u.Z (w,r)) volume 0 b := by
    obtain ⟨n,hn⟩ := hco b
    filter_upwards [u.squareZ n] with w hw
    have hsq : IntervalIntegrable (fun r => u.Z (w,r)^2) volume 0 b :=
      hw.mono_set (by simpa only [uIcc_of_le hb,uIcc_of_le (hc n)] using Icc_subset_Icc_right hn)
    have h2 : MemLp (fun r => u.Z (w,r)) 2 (volume.restrict (Ioc 0 b)) :=
      (memLp_two_iff_integrable_sq (u.measurableZ.comp measurable_prodMk_left).aestronglyMeasurable).mpr hsq.1
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hb).mpr (h2.integrable (by norm_num))
  obtain ⟨C,hC,he⟩ := ae_measurable_ito_clock_cross P B.F (B.W 0) (B.W 0) u.M (B.C 0 0)
    (B.martingale 0) u.decomposition.martingale (B.cov 0 0) u.Z u.integral True
    (by intro w r hr; simpa using B.clock 0 0 w r hr) hi
  exact ⟨C,hC,fun b hb => by simpa only [if_true] using he b hb⟩

end Asakura.Chapter6

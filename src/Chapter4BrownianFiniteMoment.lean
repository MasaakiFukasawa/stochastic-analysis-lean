import Chapter4PathMoment
import Chapter3ContinuousItoEnergy
import Chapter3LocalEnergyMaximal
import Chapter4ClockVariationIntegral

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- The precise expected squared supremum estimate used in the Picard proof,
for the constructed Ito integral on an ordinary finite real interval. -/
theorem brownian_ito_finite_path_moment
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (W C H Z : ClosedTime T → Ω → ℝ)
    (hW : LocalMProcessWitness P F W) (hC : LocalCovarianceWitness P F W W C)
    (hCm : ∀ ω, MonotoneOn (fun t => C t ω) (Iio ⊤))
    (hCc : ∀ ω t, t < ⊤ → ContinuousAt (fun s => C s ω) t)
    (hclock : ∀ ω (r : ℝ), 0 ≤ r → (r:EReal) < T → C (realTimeClamp r) ω = r)
    (hHm : ∀ t, t < ⊤ → Measurable[F t] (H t))
    (hHc : ∀ ω t, t < ⊤ → ContinuousAt (fun s => H s ω) t)
    (hZ : LocalMProcessWitness P F Z)
    (hZI : ItoCovarianceFormula P F W (fun z => H (realTimeClamp z.2) z.1) Z)
    (d : ℝ) (hd : 0 ≤ d) (hdT : (d:EReal) < T)
    (hi : Integrable (fun ω => ∫ r in 0..d, H (realTimeClamp r) ω^2) P) :
    ∃ hc : ∀ ω, Continuous (fun t => Z (min (realTimeClamp d) t) ω),
      MemLp (finiteRealPath Z d hc) 2 P ∧
      (∫ ω, ‖finiteRealPath Z d hc ω‖^2 ∂P) ≤
        4*(∫ ω, (∫ r in 0..d, H (realTimeClamp r) ω^2) ∂P) := by
  obtain ⟨hc,hm,hb⟩ := brownian_ito_maximal P hT F hF hle hnull W C H Z hW hC
    hCm hCc hclock hHm hHc hZ hZI d hd hdT hi
  have hbound := finite_real_path_memLp_bound P F hle Z d hdT hc (hZ.adapted P F)
    _ ENNReal.ofReal_lt_top hb
  have hV : 0 ≤ ∫ ω, (∫ r in 0..d, H (realTimeClamp r) ω^2) ∂P := by
    apply integral_nonneg
    intro ω
    change 0 ≤ ∫ r in 0..d, H (realTimeClamp r) ω^2
    rw [intervalIntegral.integral_of_le hd]
    exact integral_nonneg (fun r => sq_nonneg _)
  exact ⟨hc,path_square_moment_of_eLp_bound P _ _ hV hbound.2⟩

end Asakura.Chapter4

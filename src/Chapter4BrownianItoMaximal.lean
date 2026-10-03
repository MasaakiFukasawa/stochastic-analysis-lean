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

/-- The maximal L2 estimate for the actual integral of H against a
continuous local martingale whose bracket is time. Its quadratic variation
and continuous stopped path are derived, not given as extra identities. -/
theorem brownian_ito_maximal
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
      AEStronglyMeasurable (continuousPath (fun t ω => Z (min (realTimeClamp d) t) ω) hc) P ∧
      eLpNorm (continuousPath (fun t ω => Z (min (realTimeClamp d) t) ω) hc) 2 P ≤
        ENNReal.ofReal (2*Real.sqrt (∫ ω, (∫ r in 0..d, H (realTimeClamp r) ω^2) ∂P)) := by
  obtain ⟨c,hc,hcm,hcT,hct,hcut,hcc⟩ := positive_real_time_exhaustion hT
  obtain ⟨I,B,_,_,hI,hB,hBI⟩ := continuous_ito_energy_constructed P hT F hF hle hnull
    W C H Z hW hC hCm hCc hHm hHc hZ hZI c hc hcm hcT hct hcut hcc
  have ht := clock_variation_integral_all_times P C I _ c (fun n => (hc n).le) hcT
    (fun n ω r hr => hclock ω r hr.1 ((EReal.coe_le_coe hr.2).trans_lt (hcT n))) hI
  have hdt : realTimeClamp (T := T) d < ⊤ := by
    change (realTimeClamp d : EReal) < T
    rw [real_time_clamp_eq d hd hdT.le]
    exact hdT
  obtain ⟨j,hj⟩ := hcc _ hdt
  have hdc : d ≤ c j := by
    change (realTimeClamp d : EReal) < (realTimeClamp (c j) : EReal) at hj
    rw [real_time_clamp_eq d hd hdT.le,real_time_clamp_eq (c j) (hc j).le (hcT j).le] at hj
    exact EReal.coe_le_coe_iff.mp hj.le
  let V := fun ω => ∫ r in 0..d, H (realTimeClamp r) ω^2
  have hV ω : 0 ≤ V ω := by
    dsimp [V]
    rw [intervalIntegral.integral_of_le hd]
    exact integral_nonneg (fun r => sq_nonneg _)
  have hb : ∀ᵐ ω ∂P, 0 ≤ B (realTimeClamp d) ω ∧ B (realTimeClamp d) ω ≤ (1:ℝ)^2*V ω := by
    filter_upwards [hBI,ht] with ω hbω htω
    rw [hbω _ hdt,htω j d ⟨hd,hdc⟩]
    exact ⟨hV ω,by simp [V]⟩
  obtain ⟨hz,hm,hn⟩ := local_energy_maximal_bound P F hF hle hnull Z B hZ hB
    (realTimeClamp d) hdt V hi 1 (by norm_num) hb
  refine ⟨hz,hm,?_⟩
  simpa only [abs_of_nonneg (hV _),mul_one,V] using hn

end Asakura.Chapter4

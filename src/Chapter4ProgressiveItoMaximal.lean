import Chapter3ItoAllTimeEnergy
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
theorem brownian_progressive_ito_maximal
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (W C Z : ClosedTime T → Ω → ℝ) (H : Ω × ℝ → ℝ)
    (hW : LocalMProcessWitness P F W) (hC : LocalCovarianceWitness P F W W C)
    (hCm : ∀ ω, MonotoneOn (fun t => C t ω) (Iio ⊤))
    (hCc : ∀ ω t, t < ⊤ → ContinuousAt (fun s => C s ω) t)
    (hclock : ∀ ω (r : ℝ), 0 ≤ r → (r:EReal) < T → C (realTimeClamp r) ω = r)
    (hHp : ∀ R : ℝ,0≤R → (R:EReal)<T →
      @Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) R => F (realTimeClamp t.val))) inferInstance
        (fun z : Ω × Icc (0:ℝ) R => H (z.1,z.2.val)))
    (hHi : ∀ R : ℝ,0≤R → (R:EReal)<T → ∀ᵐ w ∂P,
      Integrable (fun r => H (w,r)^2) (volume.restrict (Ioc 0 R)))
    (hZ : LocalMProcessWitness P F Z)
    (hZI : ItoCovarianceFormula P F W H Z)
    (d : ℝ) (hd : 0 ≤ d) (hdT : (d:EReal) < T)
    (hi : Integrable (fun ω => ∫ r in 0..d, H (ω,r)^2) P) :
    ∃ hc : ∀ ω, Continuous (fun t => Z (min (realTimeClamp d) t) ω),
      AEStronglyMeasurable (continuousPath (fun t ω => Z (min (realTimeClamp d) t) ω) hc) P ∧
      eLpNorm (continuousPath (fun t ω => Z (min (realTimeClamp d) t) ω) hc) 2 P ≤
        ENNReal.ofReal (2*Real.sqrt (∫ ω, (∫ r in 0..d, H (ω,r)^2) ∂P)) := by
  obtain ⟨c,hc,hcm,hcT,hct,hcut,hcc⟩ := positive_real_time_exhaustion hT
  have hAm n w : MonotoneOn (fun r => C (realTimeClamp r) w) (Icc 0 (c n)) := by
    intro r hr s hs hrs
    simpa only [hclock w r hr.1 ((EReal.coe_le_coe hr.2).trans_lt (hcT n)),
      hclock w s hs.1 ((EReal.coe_le_coe hs.2).trans_lt (hcT n))] using hrs
  have hAc n w : ContinuousOn (fun r => C (realTimeClamp r) w) (Icc 0 (c n)) := by
    apply continuousOn_id.congr
    exact fun r hr => hclock w r hr.1 ((EReal.coe_le_coe hr.2).trans_lt (hcT n))
  have hmeasure (R : ℝ) (hR : 0≤R) (hRT : (R:EReal)<T) (w : Ω)
      (hm : MonotoneOn (fun r => C (realTimeClamp r) w) (Icc 0 R))
      (hc' : ContinuousOn (fun r => C (realTimeClamp r) w) (Icc 0 R)) :
      (intervalStieltjes 0 R hR (fun r => C (realTimeClamp r) w) hm
        (fun r hr => (hc' r hr).mono inter_subset_left)).measure=volume.restrict (Ioc 0 R) := by
    have he : intervalStieltjes 0 R hR (fun r => C (realTimeClamp r) w) hm
        (fun r hr => (hc' r hr).mono inter_subset_left)=
        intervalStieltjes 0 R hR id (monotone_id.monotoneOn _) (fun _ _ => continuous_id.continuousWithinAt) := by
      apply StieltjesFunction.ext
      intro r
      exact hclock w _ (intervalClamp_mem 0 R hR r).1
        ((EReal.coe_le_coe (intervalClamp_mem 0 R hR r).2).trans_lt hRT)
    rw [he,clock_stieltjes_measure]
  obtain ⟨B,hB,hBI⟩ := ito_covariance_formula_all_time_energy P hT F hF hle hnull
    W C hW hC c hc hcm hcT hct hcut hcc hAm hAc H
    (fun n => hHp (c n) (hc n).le (hcT n))
    (fun n => by
      filter_upwards [hHi (c n) (hc n).le (hcT n)] with w hw
      rw [hmeasure (c n) (hc n).le (hcT n) w (hAm n w) (hAc n w)]
      exact hw) Z hZ hZI
  have hdt : realTimeClamp (T := T) d < ⊤ := by
    change (realTimeClamp d : EReal) < T
    rw [real_time_clamp_eq d hd hdT.le]
    exact hdT
  obtain ⟨j,hj⟩ := hcc _ hdt
  have hdc : d ≤ c j := by
    change (realTimeClamp d : EReal) < (realTimeClamp (c j) : EReal) at hj
    rw [real_time_clamp_eq d hd hdT.le,real_time_clamp_eq (c j) (hc j).le (hcT j).le] at hj
    exact EReal.coe_le_coe_iff.mp hj.le
  let V := fun ω => ∫ r in 0..d, H (ω,r)^2
  have hV ω : 0 ≤ V ω := by
    dsimp [V]
    rw [intervalIntegral.integral_of_le hd]
    exact integral_nonneg (fun r => sq_nonneg _)
  obtain ⟨hDm,hDc,hbe⟩ := hBI j d hd hdc
  have hb : ∀ᵐ ω ∂P, 0 ≤ B (realTimeClamp d) ω ∧ B (realTimeClamp d) ω ≤ (1:ℝ)^2*V ω := by
    filter_upwards [hbe] with ω hbω
    rw [hbω,hmeasure d hd hdT ω (hDm ω) (hDc ω),← intervalIntegral.integral_of_le hd]
    exact ⟨hV ω,by simp [V]⟩
  obtain ⟨hz,hm,hn⟩ := local_energy_maximal_bound P F hF hle hnull Z B hZ hB
    (realTimeClamp d) hdt V hi 1 (by norm_num) hb
  refine ⟨hz,hm,?_⟩
  simpa only [abs_of_nonneg (hV _),mul_one,V] using hn

end Asakura.Chapter4

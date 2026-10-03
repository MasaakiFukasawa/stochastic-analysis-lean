import Chapter5StoppedIdentityIntegral
import Chapter2ItoCovarianceProcessFormula
import Chapter2StochasticIntervalIntegrand

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- A stopped actual integral satisfies the covariance definition of the
integral with the interval-restricted integrand. -/
theorem stopped_ito_covariance_formula
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t N,MeasurableSet[m] N → P N=0 → MeasurableSet[F t] N)
    (X Y : ClosedTime T → Ω → ℝ) (H : Ω × ℝ → ℝ)
    (hX : LocalMProcessWitness P F X) (hY : LocalMProcessWitness P F Y)
    (hH : ∀ w,Measurable (fun r => H (w,r)))
    (hy : ItoCovarianceFormula P F X H Y) (a : ℝ) (ha : 0≤a) :
    ItoCovarianceFormula P F X
      (fun z => (Ioc 0 a).indicator (fun r => H (z.1,r)) z.2)
      (fun t w => Y (min (realTimeClamp a) t) w) := by
  have hstop : ∀ t,MeasurableSet[F t] {w : Ω | realTimeClamp (T := T) a≤t} := by
    intro t
    by_cases h : realTimeClamp (T := T) a≤t <;> simp [h]
  have hYs := hY.stopped P F hF hle (fun _ => realTimeClamp a) hstop
  intro N C hN hC
  obtain ⟨D,hD,hDp⟩ := hy.finite_process_formula P F X Y H hY hH N C hN hC
  obtain ⟨E,hE⟩ := local_covariance_witness_exists P F hF hle hnull _ N hYs hN
  have he := local_covariance_one_sided_stopping P F hF hle hnull Y N D E hY hN hD
    (fun _ => realTimeClamp a) hstop hE
  refine ⟨E,hE,?_⟩
  intro d hd hdT
  obtain ⟨ν,hν,hν0,hνi,hνD⟩ := hDp d hd hdT
  refine ⟨ν,hν,hν0,?_,?_⟩
  · filter_upwards [hνi] with w hw
    exact hw.indicator measurableSet_Ioc
  · filter_upwards [he,hν0,hνi,hνD,hY.initial P F,hN.initial P F,hD.defect.initial P F]
      with w hw hn0 hni hnD hy0 hn hdef
    have hzero : D ⊥ w=0 := by
      change Y ⊥ w*N ⊥ w-D ⊥ w=0 at hdef
      simp only [hy0,hn,Pi.zero_apply,zero_mul,zero_sub] at hdef
      linarith
    have hz : realTimeClamp (T := T) 0=⊥ := by
      apply Subtype.ext
      exact real_time_clamp_eq 0 le_rfl (by simpa using hT.le)
    have hdt : realTimeClamp (T := T) d<⊤ := by
      change (realTimeClamp d:EReal)<T
      rw [real_time_clamp_eq d hd hdT.le]
      exact hdT
    have hνr : ν w=(ν w).restrict (Iic d) := by
      apply signed_stopped_interval_consistency (fun r => C (realTimeClamp r) w)
        d d hd le_rfl (ν w) (ν w) hn0 hn0
      all_goals
        intro b e hb hbe
        simpa only [real_time_clamp_mono.map_min] using hν w b e hb hbe
    let J := (Ioc 0 a).indicator (fun r => H (w,r))
    have hj : Integrable J (ν w).totalVariation := hni.indicator measurableSet_Ioc
    have hc : signedIntegralRaw (ν w) J=signedCumulative (ν w) J d := by
      calc
        _ = signedIntegralRaw ((ν w).restrict (Iic d)) J := congrArg (fun v => signedIntegralRaw v J) hνr
        _ = _ := signed_integral_restrict (ν w) measurableSet_Iic J ((hH w).indicator measurableSet_Ioc) hj.integrableOn
    have hda := hnD (min a d) ⟨le_min ha hd,min_le_right _ _⟩
    have hd0 := hnD 0 ⟨le_rfl,hd⟩
    rw [hz,hzero] at hd0
    rw [real_time_clamp_mono.map_min] at hda
    change E (realTimeClamp d) w=signedIntegralRaw (ν w) J
    rw [hw _ hdt,hc,signed_cumulative_stochastic_interval _ _ hni 0 a d ha,
      min_eq_left hd,← hd0,sub_zero,← hda]

end Asakura.Chapter5

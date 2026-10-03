import Chapter5BrownianEnergyNoise
import Chapter5ContinuousMultiplier

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 3600000
set_option backward.isDefEq.respectTransparency false

/-- The martingale term actually produced by Ito has mean-zero increments:
construct the Brownian product integral, identify it by associativity,
and derive its bracket estimate from the square envelope. -/
theorem composed_energy_noise_mean_zero
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t E, MeasurableSet[m] E → P E = 0 → MeasurableSet[F t] E)
    (W A M N : ClosedTime T → Ω → ℝ) (hW : LocalMProcessWitness P F W)
    (hA : LocalCovarianceWitness P F W W A) (hM : LocalMProcessWitness P F M) (hN : LocalMProcessWitness P F N)
    (c : ℕ → ℝ) (hc : ∀ n, 0 < c n) (hcm : StrictMono c) (hcT : ∀ n, (c n:EReal) < T)
    (hct : StrictMono (fun n => realTimeClamp (T := T) (c n)))
    (hcut : ∀ n, realTimeClamp (T := T) (c n) < ⊤)
    (hcc : ∀ t, t < ⊤ → ∃ n, t < realTimeClamp (T := T) (c n))
    (hclock : ∀ n w r, r ∈ Icc 0 (c n) → A (realTimeClamp r) w = r)
    (G H : Ω × ℝ → ℝ)
    (hG : ∀ n, @Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) (c n) => F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) (c n) => G (z.1,z.2.val)))
    (hi : ∀ n, ∀ᵐ w ∂P, IntervalIntegrable (fun r => G (w,r)^2) volume 0 (c n))
    (hGm : ∀ w, Measurable (fun r => G (w,r))) (hHm : ∀ w, Measurable (fun r => H (w,r)))
    (hHa : ∀ r : ℝ, 0 ≤ r → (r:EReal) < T → Measurable[F (realTimeClamp r)] (fun w => H (w,r)))
    (hHc : ∀ n w, ContinuousOn (fun r => H (w,r)) (Icc 0 (c n)))
    (hMG : ItoCovarianceFormula P F W G M) (hNI : ItoCovarianceFormula P F M H N)
    (R : ℝ) (hR : 0 ≤ R) (hRT : (R:EReal) < T)
    (U : Ω → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hUi : Integrable U P) (hU0 : ∀ᵐ w ∂P, 0 ≤ U w)
    (hVi : Integrable (fun w => ∫ r in 0..R, G (w,r)^2) P)
    (hbound : ∀ᵐ w ∂P, ∀ r ∈ Icc 0 R, H (w,r)^2 ≤ K^2*U w)
    (s : ClosedTime T) (hs : s ≤ realTimeClamp R) :
    Integrable (fun w => N (realTimeClamp R) w-N s w) P ∧
      (∫ w, N (realTimeClamp R) w-N s w ∂P) = 0 := by
  have hAm n w : MonotoneOn (fun r => A (realTimeClamp r) w) (Icc 0 (c n)) := by
    intro s hs t ht hst
    simpa only [hclock n w s hs,hclock n w t ht] using hst
  have hAc n w : ContinuousOn (fun r => A (realTimeClamp r) w) (Icc 0 (c n)) := by
    apply continuousOn_id.congr
    intro r hr; exact hclock n w r hr
  have hm n w : (intervalStieltjes 0 (c n) (hc n).le
      (fun r => A (realTimeClamp r) w) (hAm n w)
      (fun r hr => (hAc n w r hr).mono inter_subset_left)).measure = volume.restrict (Ioc 0 (c n)) := by
    rw [← clock_stieltjes_measure 0 (c n) (hc n).le]
    congr 1
    apply StieltjesFunction.ext
    intro r
    exact hclock n w _ (intervalClamp_mem _ _ _ _)
  have his n : ∀ᵐ w ∂P, Integrable (fun r => G (w,r)^2)
      (intervalStieltjes 0 (c n) (hc n).le
        (fun r => A (realTimeClamp r) w) (hAm n w)
        (fun r hr => (hAc n w r hr).mono inter_subset_left)).measure := by
    filter_upwards [hi n] with w hw
    rw [hm]
    exact hw.1
  obtain ⟨Z,hZ,hZI,hNZ⟩ := continuous_multiplier_ito_composition P hT F hF hle hnull
    W A M N hW hA hM hN c hc hcm hcT hct hcut hcc hAm hAc G H
    hGm hHm hG hHa hHc his hMG hNI
  have hp n := continuous_adapted_real_progressive F hF H (c n) (hc n).le
    (fun r hr => hHa r hr.1 ((EReal.coe_le_coe hr.2).trans_lt (hcT n))) (hHc n)
  have hprod n : ∀ᵐ w ∂P, IntervalIntegrable (fun r => (H (w,r)*G (w,r))^2) volume 0 (c n) := by
    filter_upwards [hi n] with w hw
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le (hc n).le).mpr
    exact continuous_multiplier_square_integrable (c n) (hc n).le _
      ((ae_restrict_mem measurableSet_Ioc).mono fun r hr => ⟨hr.1.le,hr.2⟩)
      (fun r => H (w,r)) (fun r => G (w,r)) (hHc n w) (hHm w) hw.1
  obtain ⟨hZi,hZzero⟩ := brownian_energy_noise_mean_zero P hT F hF hle hnull W A Z hW hA hZ
    c hc hcm hcT hct hcut hcc hclock G H (fun n => (hp n).mul (hG n)) hi hprod hZI
    R hR hRT U K hK hUi hU0 hVi hbound s hs
  have hRt : realTimeClamp (T := T) R < ⊤ := by
    change (realTimeClamp R : EReal) < T
    rw [real_time_clamp_eq R hR hRT.le]; exact hRT
  have he : (fun w => N (realTimeClamp R) w-N s w) =ᵐ[P] (fun w => Z (realTimeClamp R) w-Z s w) := by
    filter_upwards [hNZ] with w hw
    rw [hw _ hRt,hw _ (hs.trans_lt hRt)]
  exact ⟨hZi.congr he.symm,(integral_congr_ae he).trans hZzero⟩

end Asakura.Chapter5

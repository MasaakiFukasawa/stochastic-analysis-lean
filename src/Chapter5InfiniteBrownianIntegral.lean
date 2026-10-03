import Chapter5InfiniteTimeEnergy
import Chapter5BrownianIntegrandL2
import Chapter2ItoTerminalCharacterization

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 3600000
set_option backward.isDefEq.respectTransparency false

/-- Construct the infinite terminal Brownian integral as an L² limit from
the manuscript's actual global time-energy assumption. The integral at
infinity and its isometry are conclusions, not input values. -/
theorem brownian_infinite_terminal_integral
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t E, MeasurableSet[m] E → P E = 0 → MeasurableSet[F t] E)
    (W A : ClosedTime T → Ω → ℝ) (hW : LocalMProcessWitness P F W)
    (hA : LocalCovarianceWitness P F W W A)
    (c : ℕ → ℝ) (hc : ∀ n, 0 < c n) (hcm : StrictMono c) (hcT : ∀ n, (c n:EReal) < T)
    (hct : StrictMono (fun n => realTimeClamp (T := T) (c n)))
    (hcut : ∀ n, realTimeClamp (T := T) (c n) < ⊤)
    (hcc : ∀ t, t < ⊤ → ∃ n, t < realTimeClamp (T := T) (c n))
    (hclock : ∀ n w r, r ∈ Icc 0 (c n) → A (realTimeClamp r) w = r)
    (G : Ω × ℝ → ℝ) (hGm : Measurable G)
    (hG : ∀ n, @Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) (c n) => F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) (c n) => G (z.1,z.2.val)))
    (hco : ∀ r,∃ n,r ≤ c n)
    (hL2 : MemLp G 2 (P.prod (volume.restrict (Ioi 0)))) :
    ∃ M : ClosedTime T → Ω → ℝ,∃ hM : ContinuousM2Witness P F M,
      LocalMProcessWitness P F M ∧ ItoCovarianceFormula P F W G M ∧
      ‖(hM.moment ⊤).toLp (M ⊤)‖^2 = ∫ w,(∫ r in Ioi 0,G (w,r)^2) ∂P ∧
      Tendsto (fun t => eLpNorm (M t-M ⊤) 2 P) (𝓝[<] (⊤ : ClosedTime T)) (𝓝 0) := by
  obtain ⟨hCT,hGi,hlim⟩ := infinite_time_energy_limit P G hGm hL2 c (fun n => (hc n).le) hcm.monotone hco
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
  have hi n : ∀ᵐ w ∂P,Integrable (fun r => G (w,r)^2)
      (intervalStieltjes 0 (c n) (hc n).le
        (fun r => A (realTimeClamp r) w) (hAm n w)
        (fun r hr => (hAc n w r hr).mono inter_subset_left)).measure := by
    filter_upwards [hGi n] with w hw
    rw [hm]
    exact hw.1
  have hl : ∀ᵐ w ∂P,Tendsto (fun n => ∫ r,G (w,r)^2
      ∂(intervalStieltjes 0 (c n) (hc n).le
        (fun r => A (realTimeClamp r) w) (hAm n w)
        (fun r hr => (hAc n w r hr).mono inter_subset_left)).measure) atTop
      (𝓝 (∫ r in Ioi 0,G (w,r)^2)) := by
    simpa only [hm,intervalIntegral.integral_of_le (hc _).le] using hlim
  obtain ⟨M,hM,hMl,hMI,hiso,Y,hY,hYL⟩ := ito_terminal_isometry_and_covariance_constructed
    P hT F hF hle hnull W A hW hA c hc hcm hcT hct hcut hcc hAm hAc G hG hi
    (fun w => ∫ r in Ioi 0,G (w,r)^2) hCT hl
  refine ⟨M,hM,hMl,hMI,hiso,?_⟩
  apply hYL.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact eLpNorm_congr_ae ((hY t ht).symm.sub EventuallyEq.rfl)

end Asakura.Chapter5

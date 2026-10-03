import Chapter5InfiniteTimeEnergy
import Chapter5BrownianIntegrandL2
import Chapter2ItoCharacterizedConstruction

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 3600000
set_option backward.isDefEq.respectTransparency false

/-- Local pathwise square integrability suffices for the actual Brownian Ito integral; no expected energy is assumed. -/
theorem brownian_local_path_energy_integral_constructed
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
    (hGi : ∀ j,∀ᵐ w ∂P,IntervalIntegrable (fun r => G (w,r)^2) volume 0 (c j)) :
    ∃ M : ClosedTime T → Ω → ℝ,
      LocalMProcessWitness P F M ∧ ItoCovarianceFormula P F W G M := by
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
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (hc n).le).mp hw
  exact ito_integral_exists_with_covariance_characterization P hT F hF hle hnull W A hW hA
    c hc hcm hcT hct hcut hcc hAm hAc G hG hi

end Asakura.Chapter5

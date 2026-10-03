import Chapter3ItoAllTimeEnergy
import Chapter4ClockVariationIntegral

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

/-- The quadratic variation of the actual Brownian integral is the
ordinary integral of sigma², with merely progressive sigma and local
square integrability. This supplies the PDE proof's general coefficient. -/
theorem clock_ito_integral_bracket
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t E, MeasurableSet[m] E → P E = 0 → MeasurableSet[F t] E)
    (W A X : ClosedTime T → Ω → ℝ) (hW : LocalMProcessWitness P F W)
    (hA : LocalCovarianceWitness P F W W A) (hX : LocalMProcessWitness P F X)
    (c : ℕ → ℝ) (hc : ∀ n, 0 < c n) (hcm : StrictMono c) (hcT : ∀ n, (c n:EReal) < T)
    (hct : StrictMono (fun n => realTimeClamp (T := T) (c n)))
    (hcut : ∀ n, realTimeClamp (T := T) (c n) < ⊤)
    (hcc : ∀ t, t < ⊤ → ∃ n, t < realTimeClamp (T := T) (c n))
    (hclock : ∀ n w r, r ∈ Icc 0 (c n) → A (realTimeClamp r) w = r)
    (G : Ω × ℝ → ℝ)
    (hG : ∀ n, @Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) (c n) => F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) (c n) => G (z.1,z.2.val)))
    (hi : ∀ n, ∀ᵐ w ∂P, IntervalIntegrable (fun r => G (w,r)^2) volume 0 (c n))
    (hXI : ItoCovarianceFormula P F W G X) :
    ∃ B : ClosedTime T → Ω → ℝ, LocalCovarianceWitness P F X X B ∧
      ∀ d : ℝ, 0 ≤ d → (d:EReal) < T →
        B (realTimeClamp d) =ᵐ[P] fun w => ∫ r in 0..d, G (w,r)^2 := by
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
  obtain ⟨B,hB,he⟩ := ito_covariance_formula_all_time_energy P hT F hF hle hnull
    W A hW hA c hc hcm hcT hct hcut hcc hAm hAc G hG his X hX hXI
  refine ⟨B,hB,?_⟩
  intro d hd hdT
  have hdt : realTimeClamp (T := T) d < ⊤ := by
    change (realTimeClamp d : EReal) < T
    rw [real_time_clamp_eq d hd hdT.le]; exact hdT
  obtain ⟨j,hj⟩ := hcc _ hdt
  have hdj : d ≤ c j := by
    change (realTimeClamp d : EReal) < (realTimeClamp (c j) : EReal) at hj
    rw [real_time_clamp_eq d hd hdT.le,real_time_clamp_eq (c j) (hc j).le (hcT j).le] at hj
    exact EReal.coe_le_coe_iff.mp hj.le
  obtain ⟨hDm,hDc,heq⟩ := he j d hd hdj
  filter_upwards [heq] with w hw
  rw [hw]
  have hm' : intervalStieltjes 0 d hd (fun r => A (realTimeClamp r) w) (hDm w)
      (fun r hr => (hDc w r hr).mono inter_subset_left) =
      intervalStieltjes 0 d hd id (monotone_id.monotoneOn _) (fun _ _ => continuous_id.continuousWithinAt) := by
    apply StieltjesFunction.ext
    intro r
    exact hclock j w _ (Icc_subset_Icc_right hdj (intervalClamp_mem _ _ _ _))
  rw [hm',clock_stieltjes_integral]

end Asakura.Chapter5

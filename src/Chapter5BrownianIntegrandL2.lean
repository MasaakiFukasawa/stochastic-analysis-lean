import Chapter5BrownianIntegralBracket
import Chapter5FiniteTimeEnergy

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 3600000
set_option backward.isDefEq.respectTransparency false

/-- The integrand produced by local martingale representation really is
in the finite-time L² space when the represented martingale is M².
This supplies the omitted finite-energy justification in the frozen step. -/
theorem brownian_integrand_L2_of_M2
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
    (G : Ω × ℝ → ℝ) (hGm : Measurable G)
    (hG : ∀ n, @Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) (c n) => F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) (c n) => G (z.1,z.2.val)))
    (hi : ∀ n, ∀ᵐ w ∂P, IntervalIntegrable (fun r => G (w,r)^2) volume 0 (c n))
    (hXI : ItoCovarianceFormula P F W G X)
    (R : ℝ) (hR : 0 ≤ R) (hRT : (R:EReal) < T)
    (hstop : ContinuousM2Witness P F (fun t w => X (min (realTimeClamp R) t) w)) :
    MemLp G 2 (P.prod (volume.restrict (Ioc 0 R))) ∧
      (∫ w,X (realTimeClamp R) w^2 ∂P) = ∫ w,(∫ r in 0..R,G (w,r)^2) ∂P := by
  obtain ⟨Q,hQ,hQI⟩ := clock_ito_integral_bracket P hT F hF hle hnull
    W A X hW hA hX c hc hcm hcT hct hcut hcc hclock G hG hi hXI
  have hRt : realTimeClamp (T := T) R < ⊤ := by
    change (realTimeClamp R : EReal) < T
    rw [real_time_clamp_eq R hR hRT.le]; exact hRT
  have hσ : ∀ t,MeasurableSet[F t] {w : Ω | realTimeClamp (T := T) R ≤ t} := by
    intro t
    by_cases h : realTimeClamp (T := T) R ≤ t <;> simp [h]
  obtain ⟨hQi,he⟩ := stopped_M2_energy P F hF hle hnull X Q hX hQ
    (fun _ => realTimeClamp R) hσ (fun _ => hRt) hstop
  have hGi : Integrable (fun w => ∫ r in 0..R,G (w,r)^2) P := hQi.congr (hQI R hR hRT)
  refine ⟨?_,he.trans (integral_congr_ae (hQI R hR hRT))⟩
  obtain ⟨j,hj⟩ := hcc _ hRt
  have hRj : R ≤ c j := by
    change (realTimeClamp R : EReal) < (realTimeClamp (c j) : EReal) at hj
    rw [real_time_clamp_eq R hR hRT.le,real_time_clamp_eq (c j) (hc j).le (hcT j).le] at hj
    exact EReal.coe_le_coe_iff.mp hj.le
  apply (memLp_two_iff_integrable_sq hGm.aestronglyMeasurable).mpr
  apply (integrable_prod_iff (hGm.pow_const 2).aestronglyMeasurable).mpr
  constructor
  · filter_upwards [hi j] with w hw
    have hir : IntervalIntegrable (fun r => G (w,r)^2) volume 0 R :=
      hw.mono_set (by simpa [uIcc_of_le hR,uIcc_of_le (hc j).le] using Icc_subset_Icc_right hRj)
    exact hir.1
  · simpa only [Real.norm_eq_abs,abs_sq,intervalIntegral.integral_of_le hR] using hGi

end Asakura.Chapter5

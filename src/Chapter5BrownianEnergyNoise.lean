import Chapter5BrownianIntegralBracket
import Chapter5EnergyNoise

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 3600000
set_option backward.isDefEq.respectTransparency false

/-- Derive the energy martingale's bracket bound from its actual Brownian
integral, then apply the p=1 martingale theorem and Cauchy--Schwarz.
The zero expectation used in the BSDE estimate is a conclusion. -/
theorem brownian_energy_noise_mean_zero
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t E, MeasurableSet[m] E → P E = 0 → MeasurableSet[F t] E)
    (W A N : ClosedTime T → Ω → ℝ) (hW : LocalMProcessWitness P F W)
    (hA : LocalCovarianceWitness P F W W A) (hN : LocalMProcessWitness P F N)
    (c : ℕ → ℝ) (hc : ∀ n, 0 < c n) (hcm : StrictMono c) (hcT : ∀ n, (c n:EReal) < T)
    (hct : StrictMono (fun n => realTimeClamp (T := T) (c n)))
    (hcut : ∀ n, realTimeClamp (T := T) (c n) < ⊤)
    (hcc : ∀ t, t < ⊤ → ∃ n, t < realTimeClamp (T := T) (c n))
    (hclock : ∀ n w r, r ∈ Icc 0 (c n) → A (realTimeClamp r) w = r)
    (G H : Ω × ℝ → ℝ)
    (hG : ∀ n, @Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) (c n) => F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) (c n) => H (z.1,z.2.val)*G (z.1,z.2.val)))
    (hi : ∀ n, ∀ᵐ w ∂P, IntervalIntegrable (fun r => G (w,r)^2) volume 0 (c n))
    (hprod : ∀ n, ∀ᵐ w ∂P, IntervalIntegrable (fun r => (H (w,r)*G (w,r))^2) volume 0 (c n))
    (hNI : ItoCovarianceFormula P F W (fun z => H z*G z) N)
    (R : ℝ) (hR : 0 ≤ R) (hRT : (R:EReal) < T)
    (U : Ω → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hUi : Integrable U P) (hU0 : ∀ᵐ w ∂P, 0 ≤ U w)
    (hVi : Integrable (fun w => ∫ r in 0..R, G (w,r)^2) P)
    (hbound : ∀ᵐ w ∂P, ∀ r ∈ Icc 0 R, H (w,r)^2 ≤ K^2*U w)
    (s : ClosedTime T) (hs : s ≤ realTimeClamp R) :
    Integrable (fun w => N (realTimeClamp R) w-N s w) P ∧
      (∫ w, N (realTimeClamp R) w-N s w ∂P) = 0 := by
  obtain ⟨Q,hQ,hQI⟩ := clock_ito_integral_bracket P hT F hF hle hnull
    W A N hW hA hN c hc hcm hcT hct hcut hcc hclock (fun z => H z*G z) hG hprod hNI
  have hRt : realTimeClamp (T := T) R < ⊤ := by
    change (realTimeClamp R : EReal) < T
    rw [real_time_clamp_eq R hR hRT.le]; exact hRT
  obtain ⟨j,hj⟩ := hcc _ hRt
  have hRj : R ≤ c j := by
    change (realTimeClamp R : EReal) < (realTimeClamp (c j) : EReal) at hj
    rw [real_time_clamp_eq R hR hRT.le,real_time_clamp_eq (c j) (hc j).le (hcT j).le] at hj
    exact EReal.coe_le_coe_iff.mp hj.le
  have hQb : ∀ᵐ w ∂P, Q (realTimeClamp R) w ≤ K^2*U w*(∫ r in 0..R,G (w,r)^2) := by
    filter_upwards [hQI R hR hRT,hi j,hprod j,hbound] with w he hgi hpi hb
    have hg : IntervalIntegrable (fun r => G (w,r)^2) volume 0 R :=
      hgi.mono_set (by simpa [uIcc_of_le hR,uIcc_of_le (hc j).le] using Icc_subset_Icc_right hRj)
    have hp : IntervalIntegrable (fun r => (H (w,r)*G (w,r))^2) volume 0 R :=
      hpi.mono_set (by simpa [uIcc_of_le hR,uIcc_of_le (hc j).le] using Icc_subset_Icc_right hRj)
    rw [he,← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hR hp (hg.const_mul (K^2*U w))
    intro r hr
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right (hb r hr) (sq_nonneg _)
  exact energy_noise_increment_mean_zero P hT F hF hle hnull N Q hN hQ
    (realTimeClamp R) hRt U (fun w => ∫ r in 0..R,G (w,r)^2) K hK hUi hVi hU0
    (ae_of_all _ fun w => intervalIntegral.integral_nonneg hR (fun r _ => sq_nonneg _)) hQb s hs

end Asakura.Chapter5

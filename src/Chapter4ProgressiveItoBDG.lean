import Chapter5BrownianIntegralBracket
import Chapter3BDG
import Chapter4FinitePathLift

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter5
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false

/-- The BDG step in the moment proof with a merely progressive,
locally square-integrable coefficient. -/
theorem progressive_brownian_ito_bdg
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
    (hXI : ItoCovarianceFormula P F W G X)
    (d : ℝ) (hd : 0≤d) (hdT : (d:EReal)<T) (p : ℝ) (hp : 0<p) :
    (∫⁻ w,(ENNReal.ofReal (runningMaximum X (hX.path P F) (realTimeClamp d) w))^p ∂P)≤
      ENNReal.ofReal (bdgUpperMomentConstant p)*
        (∫⁻ w,(ENNReal.ofReal (∫ r in 0..d,G (w,r)^2))^(p/2) ∂P) := by
  obtain ⟨B,hB,he⟩ := clock_ito_integral_bracket P hT F hF hle hnull W A X hW hA hX
    c hc hcm hcT hct hcut hcc hclock G hG hi hXI
  have hb := (bdg_lintegrals P hT F hF hle hnull X B hX hB p hp
    (realTimeClamp d) (real_time_below d hd hdT)).1
  have hei : (∫⁻ w,(ENNReal.ofReal (B (realTimeClamp d) w))^(p/2) ∂P)=
      ∫⁻ w,(ENNReal.ofReal (∫ r in 0..d,G (w,r)^2))^(p/2) ∂P := by
    apply lintegral_congr_ae
    exact (he d hd hdT).mono (fun w hw => congrArg (fun x : ℝ => (ENNReal.ofReal x)^(p/2)) hw)
  simpa only [hei] using hb

end Asakura.Chapter4

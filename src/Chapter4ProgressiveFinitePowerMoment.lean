import Chapter4PowerMomentBridge

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter5
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

/-- Actual finite-path p moment for the progressive Brownian integral. -/
theorem progressive_ito_finite_power_moment
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
    (d : ℝ) (hd : 0≤d) (hdT : (d:EReal)<T) (p : ℝ) (hp : 0<p)
    (henergy : Integrable (fun w => (∫ r in 0..d,G (w,r)^2)^(p/2)) P) :
    ∃ hs : ∀ w,Continuous (fun t => X (min (realTimeClamp d) t) w),
      MemLp (finiteRealPath X d hs) (ENNReal.ofReal p) P ∧
      (∫ w,‖finiteRealPath X d hs w‖^p ∂P)≤
        bdgUpperMomentConstant p*(∫ w,(∫ r in 0..d,G (w,r)^2)^(p/2) ∂P) := by
  let hs := open_path_stopped_continuous X (hX.path P F) d hd hdT
  have hm := finite_real_path_measurable F hle X d hdT hs (hX.adapted P F)
  have hv w : 0≤(∫ r in 0..d,G (w,r)^2)^(p/2) := Real.rpow_nonneg
    (intervalIntegral.integral_nonneg_of_forall hd (fun _ => sq_nonneg _)) _
  have hb := progressive_brownian_ito_bdg P hT F hF hle hnull W A X hW hA hX
    c hc hcm hcT hct hcut hcc hclock G hG hi hXI d hd hdT p hp
  have hfinite : (∫⁻ w,(ENNReal.ofReal ‖finiteRealPath X d hs w‖)^p ∂P)≤
      ENNReal.ofReal (bdgUpperMomentConstant p)*(∫⁻ w,ENNReal.ofReal ((∫ r in 0..d,G (w,r)^2)^(p/2)) ∂P) := by
    simp_rw [finite_real_path_norm_eq_runningMaximum X (hX.path P F) d hd hdT hs,
      ← ENNReal.ofReal_rpow_of_nonneg (intervalIntegral.integral_nonneg_of_forall hd (fun _ => sq_nonneg _)) (by positivity : 0≤p/2)]
    exact hb
  exact ⟨hs,power_moment_of_lintegral_bound P _ hm.aestronglyMeasurable p hp _ henergy hv
    _ (bdg_moment_constants_positive p hp).1.le hfinite⟩

end Asakura.Chapter4

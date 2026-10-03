import Chapter3BDG
import Chapter3RunningMaximumStopping

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false

/-- BDG and monotone convergence on deterministic finite horizons give the
Lp running maximum of a process stopped strictly before T. -/
theorem stopped_path_memLp_of_variation_moment
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X A : ClosedTime T → Ω → ℝ)
    (hX : LocalMProcessWitness P F X) (hA : LocalCovarianceWitness P F X X A)
    (τ : Ω → ClosedTime T) (hτ : ∀ t, MeasurableSet[F t] {ω | τ ω ≤ t})
    (hτt : ∀ ω, τ ω < ⊤) (p : ℝ) (hp : 0 < p)
    (hAi : Integrable (fun ω => A (τ ω) ω^(p/2)) P) :
    ∃ hc : ∀ ω, Continuous (fun t => X (min (τ ω) t) ω),
      MemLp (continuousPath (fun t ω => X (min (τ ω) t) ω) hc) (ENNReal.ofReal p) P := by
  obtain ⟨Q,hQ,hQm,hQc,hQ0⟩ := local_quadratic_variation_regular_choice P F hF hle hnull X hX
  have he := hA.unique P F hF hle hQ
  have hQi : Integrable (fun ω => Q (τ ω) ω^(p/2)) P := hAi.congr
    (he.mono (fun ω hω => congrArg (fun x : ℝ => x^(p/2)) (hω (τ ω) (hτt ω))))
  have hQp ω t (ht : t < ⊤) : 0 ≤ Q t ω := by rw [← hQ0 ω]; exact hQm ω hT ht bot_le
  let Y := fun t ω => X (min (τ ω) t) ω
  let B := fun t ω => Q (min (τ ω) t) ω
  have hY := hX.stopped P F hF hle τ hτ
  have hB := hQ.stopped P F hF hle τ hτ
  obtain ⟨hYa,hYc⟩ := hX.stopped_regular P F hF hle τ hτ hτt
  have hYm := continuous_path_measurable Y hYc (fun t => (hYa t).mono (hle t) le_rfl)
  obtain ⟨c,_,_,_,hcm,hct,hcc⟩ := positive_real_time_exhaustion hT
  let f := fun n ω => (ENNReal.ofReal (runningMaximum Y (hY.path P F) (realTimeClamp (c n)) ω))^p
  let fLim := fun ω => (ENNReal.ofReal ‖continuousPath Y hYc ω‖)^p
  have hfm n : Measurable (f n) :=
    (((runningMaximum_adapted F hF Y (hY.path P F) (hY.adapted P F) _ (hct n)).mono
      (hle _) le_rfl).ennreal_ofReal).pow_const p
  have hmono ω : Monotone (fun n => f n ω) := by
    intro n k hnk
    exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal
      (runningMaximum_monotone Y (hY.path P F) ω (hct n) (hct k) (hcm.monotone hnk))) hp.le
  have hconv ω : Tendsto (fun n => f n ω) atTop (𝓝 (fLim ω)) := by
    obtain ⟨N,hN⟩ := hcc (τ ω) (hτt ω)
    apply tendsto_const_nhds.congr'
    apply eventually_atTop.mpr
    refine ⟨N,?_⟩
    intro n hn
    have htn : τ ω ≤ realTimeClamp (T := T) (c n) := hN.le.trans (hcm.monotone hn)
    dsimp only [f,fLim]
    rw [runningMaximum_stopped X (hX.path P F) τ (hY.path P F) _ (hct n) ω,min_eq_left htn,
      runningMaximum_of_lt_top X (hX.path P F) (τ ω) (hτt ω) ω]
    rfl
  have hlim := lintegral_tendsto_of_tendsto_of_monotone (μ := P) (fun n => (hfm n).aemeasurable)
    (Filter.Eventually.of_forall hmono) (Filter.Eventually.of_forall hconv)
  let V := ∫⁻ ω, (ENNReal.ofReal (Q (τ ω) ω))^(p/2) ∂P
  have hbound n : (∫⁻ ω, f n ω ∂P) ≤ ENNReal.ofReal (bdgUpperMomentConstant p)*V := by
    have hh := (bdg_lintegrals P hT F hF hle hnull Y B hY hB p hp _ (hct n)).1
    apply hh.trans
    apply mul_le_mul' le_rfl
    apply lintegral_mono
    intro ω
    apply ENNReal.rpow_le_rpow _ (by positivity : 0 ≤ p/2)
    exact ENNReal.ofReal_le_ofReal (hQm ω ((min_le_left (τ ω) _).trans_lt (hτt ω)) (hτt ω) (min_le_left _ _))
  have hfinal := le_of_tendsto hlim (Filter.Eventually.of_forall hbound)
  have hVfinite : V < ∞ := by
    have heV : V = ENNReal.ofReal (∫ ω, Q (τ ω) ω^(p/2) ∂P) := by
      dsimp [V]
      rw [ofReal_integral_eq_lintegral_ofReal hQi
        (Filter.Eventually.of_forall (fun ω => Real.rpow_nonneg (hQp ω (τ ω) (hτt ω)) _))]
      apply lintegral_congr
      intro ω
      exact ENNReal.ofReal_rpow_of_nonneg (hQp ω _ (hτt ω)) (by positivity)
    rw [heV]
    exact ENNReal.ofReal_lt_top
  have hfinite := hfinal.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hVfinite)
  refine ⟨hYc,?_⟩
  change eLpNorm (continuousPath Y hYc) (ENNReal.ofReal p) P < ∞
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simp [hp]) (by simp) hYm.aestronglyMeasurable]
  simp only [ENNReal.toReal_ofReal hp.le,← ofReal_norm]
  exact ENNReal.rpow_lt_top_of_nonneg (by positivity : 0 ≤ 1/p) hfinite.ne

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.stopped_path_memLp_of_variation_moment

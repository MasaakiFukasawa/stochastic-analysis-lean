import Chapter3BDGBoundedLintegral
import Chapter3RunningMaximumStopping
import Chapter3QuadraticApproximationLocalizers
import Chapter2StoppedRegularity

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 3600000
set_option backward.isDefEq.respectTransparency false

/-- Remove both boundedness assumptions by the manuscript's common stopping
times and monotone convergence. No finite moment assumption remains. -/
theorem bdg_lintegrals_regular
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X A : ClosedTime T → Ω → ℝ)
    (hX : LocalMProcessWitness P F X) (hA : LocalCovarianceWitness P F X X A)
    (hAm : ∀ ω, MonotoneOn (fun t => A t ω) (Iio ⊤))
    (hAc : ∀ ω t, t < ⊤ → ContinuousAt (fun s => A s ω) t)
    (hA0 : ∀ ω, A ⊥ ω = 0)
    (p : ℝ) (hp : 0 < p) (b : ClosedTime T) (hb : b < ⊤) :
    (∫⁻ ω, (ENNReal.ofReal (runningMaximum X (hX.path P F) b ω))^p ∂P) ≤
      ENNReal.ofReal (bdgUpperMomentConstant p)*(∫⁻ ω, (ENNReal.ofReal (A b ω))^(p/2) ∂P) ∧
    (∫⁻ ω, (ENNReal.ofReal (A b ω))^(p/2) ∂P) ≤
      ENNReal.ofReal (bdgReverseMomentConstant p)*(∫⁻ ω, (ENNReal.ofReal (runningMaximum X (hX.path P F) b ω))^p ∂P) := by
  obtain ⟨c,_,_,_,hct,hcut,hcc⟩ := positive_real_time_exhaustion hT
  obtain ⟨σ,hσ,hσm,hσt,hσco,hσb⟩ := quadratic_approximation_bounded_localizers P F hF hle hnull
    X A X hX hA (hX.adapted P F) (hX.path P F) (fun n => realTimeClamp (c n)) hct.monotone hcut hcc
  let Xn := fun n t ω => X (min (σ n ω) t) ω
  let An := fun n t ω => A (min (σ n ω) t) ω
  have hXn n : LocalMProcessWitness P F (Xn n) := hX.stopped P F hF hle (σ n) (hσ n)
  have hAn n : LocalCovarianceWitness P F (Xn n) (Xn n) (An n) := hA.stopped P F hF hle (σ n) (hσ n)
  have hAnm n ω : MonotoneOn (fun t => An n t ω) (Iio ⊤) := by
    intro s hs t ht hst
    exact hAm ω ((min_le_right (σ n ω) s).trans_lt hs) ((min_le_right (σ n ω) t).trans_lt ht)
      (min_le_min_left (σ n ω) hst)
  have hAnc n ω t (ht : t < ⊤) : ContinuousAt (fun s => An n s ω) t :=
    (hAc ω _ ((min_le_left (σ n ω) t).trans_lt (hσt n ω))).comp
      (continuous_const.min continuous_id).continuousAt
  have hAn0 n ω : An n ⊥ ω = 0 := by simpa only [An,min_bot_right] using hA0 ω
  have hbn n : ∀ᵐ ω ∂P, An n b ω ≤ (n:ℝ) := (hσb n).mono (fun ω hω => (hω b).2.2)
  have hxn n : ∀ᵐ ω ∂P, ∀ s, s ≤ b → |Xn n s ω| ≤ (n:ℝ) := by
    filter_upwards [hσb n,hX.initial P F] with ω hω h0
    intro s hs
    have h := (hω s).1
    simpa only [Xn,h0,Pi.zero_apply,sub_zero] using h
  have hineq n := bounded_bdg_lintegrals P hT F hF hle hnull (Xn n) (An n) (hXn n) (hAn n)
    (hAnm n) (hAnc n) (hAn0 n) p hp b hb (n:ℝ) (n:ℝ) (by positivity) (by positivity) (hbn n) (hxn n)
  let f := fun n ω => (ENNReal.ofReal (runningMaximum (Xn n) ((hXn n).path P F) b ω))^p
  let g := fun n ω => (ENNReal.ofReal (An n b ω))^(p/2)
  let fLim := fun ω => (ENNReal.ofReal (runningMaximum X (hX.path P F) b ω))^p
  let gLim := fun ω => (ENNReal.ofReal (A b ω))^(p/2)
  have heS n ω : runningMaximum (Xn n) ((hXn n).path P F) b ω =
      runningMaximum X (hX.path P F) (min (σ n ω) b) ω :=
    runningMaximum_stopped X (hX.path P F) (σ n) ((hXn n).path P F) b hb ω
  have hfm n : Measurable (f n) :=
    (((runningMaximum_adapted F hF (Xn n) ((hXn n).path P F) ((hXn n).adapted P F) b hb).mono
      (hle b) le_rfl).ennreal_ofReal).pow_const p
  have hgm n : Measurable (g n) :=
    (((hAn n).adapted P F (hXn n) (hXn n) b hb).mono (hle b) le_rfl).ennreal_ofReal.pow_const (p/2)
  have hfm' ω : Monotone (fun n => f n ω) := by
    intro n k hnk
    apply ENNReal.rpow_le_rpow _ hp.le
    apply ENNReal.ofReal_le_ofReal
    rw [heS n ω,heS k ω]
    exact runningMaximum_monotone X (hX.path P F) ω
      ((min_le_right (σ n ω) b).trans_lt hb) ((min_le_right (σ k ω) b).trans_lt hb)
      (min_le_min_right b (hσm ω hnk))
  have hgm' ω : Monotone (fun n => g n ω) := by
    intro n k hnk
    apply ENNReal.rpow_le_rpow _ (by positivity : 0 ≤ p/2)
    exact ENNReal.ofReal_le_ofReal (hAm ω
      ((min_le_right (σ n ω) b).trans_lt hb) ((min_le_right (σ k ω) b).trans_lt hb)
      (min_le_min_right b (hσm ω hnk)))
  have hev ω : ∀ᶠ n in atTop, min (σ n ω) b = b := by
    obtain ⟨N,hN⟩ := hσco ω b hb
    exact eventually_atTop.mpr ⟨N,fun n hn => min_eq_right (hN.le.trans (hσm ω hn))⟩
  have hfl ω : Tendsto (fun n => f n ω) atTop (𝓝 (fLim ω)) := by
    have he : (fun _ : ℕ => fLim ω) =ᶠ[atTop] (fun n => f n ω) := by
      filter_upwards [hev ω] with n hn
      dsimp only [f,fLim]
      rw [heS n ω,hn]
    exact tendsto_const_nhds.congr' he
  have hgl ω : Tendsto (fun n => g n ω) atTop (𝓝 (gLim ω)) := by
    have he : (fun _ : ℕ => gLim ω) =ᶠ[atTop] (fun n => g n ω) := by
      filter_upwards [hev ω] with n hn
      simp only [g,gLim,An,hn]
    exact tendsto_const_nhds.congr' he
  have hfi := lintegral_tendsto_of_tendsto_of_monotone (μ := P) (fun n => (hfm n).aemeasurable)
    (Filter.Eventually.of_forall hfm') (Filter.Eventually.of_forall hfl)
  have hgi := lintegral_tendsto_of_tendsto_of_monotone (μ := P) (fun n => (hgm n).aemeasurable)
    (Filter.Eventually.of_forall hgm') (Filter.Eventually.of_forall hgl)
  constructor
  · exact le_of_tendsto_of_tendsto hfi (ENNReal.Tendsto.const_mul hgi (Or.inr (by simp)))
      (Filter.Eventually.of_forall (fun n => (hineq n).1))
  · exact le_of_tendsto_of_tendsto hgi (ENNReal.Tendsto.const_mul hfi (Or.inr (by simp)))
      (Filter.Eventually.of_forall (fun n => (hineq n).2))

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.bdg_lintegrals_regular

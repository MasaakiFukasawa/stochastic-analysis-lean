import Chapter7RandomTimeTerminal
import Chapter2HalfLineLocalization

open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- An actual closed M2 martingale, sampled at increasing stopping times,
is local for the stopped-sigma changed filtration when the sampled paths
are continuous. All moments and martingale identities follow from optional
sampling and conditional expectation of the original terminal value. -/
theorem random_time_raw_closed_martingale_local
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)]
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t ≤ m)
    (X : ClosedTime T → Ω → ℝ) (hX : ContinuousM2Witness P F X)
    (τ : ℝ → Ω → ClosedTime T) (hτ : ∀ s t,MeasurableSet[F t] {w | τ s w ≤ t})
    (hm : ∀ w,Monotone (fun s => τ s w)) (hz : ∀ w,τ 0 w = ⊥)
    (hBc : ∀ w,Continuous (fun s => X (τ s w) w)) :
    let G := fun s : ℝ≥0 => writtenStoppedSpace m F (τ s) (hτ s)
    LocalMProcessWitness P (halfClosedFiltration m G)
      (fun t w => X (τ (halfTimeReal t) w) w) := by
  let H := fun r => writtenStoppedSpace m F (τ r) (hτ r)
  let G := fun s : ℝ≥0 => H s
  have hHm : Monotone H := fun a b hab => written_stoppedSpace_mono m F
    (τ a) (τ b) (hτ a) (hτ b) (fun w => hm w hab)
  have hGm : Monotone G := fun s t hst => hHm hst
  have hGl s : G s ≤ m := fun _ he => he.1
  have hBa (s : ℝ≥0) : Measurable[G s] (fun w => X (τ s w) w) :=
    random_time_adapted (Fact.out : 0 ≤ T) F hF hle X hX.adapted hX.path τ hτ s
  have hce (s : ℝ≥0) : P[X ⊤|G s] =ᵐ[P] (fun w => X (τ s w) w) := by
    exact (continuous_closed_optional_written P (Fact.out : 0 ≤ T) F hF hle (τ s) (hτ s) X hX.adapted
      (fun w t => (hX.path w).continuousAt.continuousWithinAt)
      ((hX.adapted ⊤).mono (hle ⊤) le_rfl) ((hX.moment ⊤).integrable (by norm_num))
      (fun t => (hX.martingale t ⊤ le_top).symm)).symm
  apply half_line_martingale_local P G hGm hGl (fun s w => X (τ s w) w) hBa
  · intro s
    exact ((hX.moment ⊤).condExp (by norm_num : (1:ℝ≥0∞) ≤ 2)).ae_eq (hce s)
  · intro w
    exact (hBc w).comp NNReal.continuous_coe
  · intro s t hst
    exact (condExp_congr_ae (hce t).symm).trans
      ((condExp_condExp_of_le (hGm hst) (hGl t)).trans (hce s))
  · simpa only [NNReal.coe_zero,hz] using hX.initial

end Asakura.Chapter7

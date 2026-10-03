import FullAuditStoppedContinuous
import Chapter2WrittenLimit
import Chapter1WrittenAsano

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.FullAudit
open Asakura.Chapter1Written Asakura.Chapter2Written

/-- The manuscript's terminal-value proof: finite grids, backward L1 convergence,
 right-continuous paths, Fatou identification and C5. All grid hypotheses and
 stopped measurability are discharged for the actual process and stopping time. -/
theorem continuous_closed_optional_written {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] {T : EReal} (hT : 0 ≤ T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (τ : Ω → ClosedTime T) (hτ : ∀ t, MeasurableSet[F t] {ω | τ ω ≤ t})
    (X : ClosedTime T → Ω → ℝ) (hX : ∀ t, Measurable[F t] (X t))
    (hr : ∀ ω t, ContinuousWithinAt (fun s => X s ω) (Ici t) t)
    {Y : Ω → ℝ} (hmY : Measurable[m] Y) (hY : Integrable Y P)
    (hc : ∀ t, X t =ᵐ[P] P[Y | F t]) :
    (fun ω => X (τ ω) ω) =ᵐ[P] P[Y | writtenStoppedSpace m F τ hτ] := by
  let τn := fun n ω => gridTime n (τ ω)
  let hn := fun n => gridTime_stopping F hF τ hτ n
  let G := fun n => writtenStoppedSpace m F (τn n) (hn n)
  have hgrid (n : ℕ) : (fun ω => X (τn n ω) ω) =ᵐ[P] P[Y | G n] := by
    apply optional_sampling_countable_range P F hF hle (τn n) (hn n) _ hY X hc
    apply (gridTime_finite_range T n).countable.mono
    rintro s ⟨ω,rfl⟩
    exact mem_range_self (τ ω)
  have hsig := grid_stopped_sigmas m F hF τ hτ
  apply written_backward_stop_identification G hsig.1 (fun n A hA => hA.1)
    (writtenStoppedSpace m F τ hτ) hsig.2 hmY hY
    (stopped_value_measurable_right_continuous m hT F hF hle τ hτ X hX hr).stronglyMeasurable
  filter_upwards [ae_all_iff.mpr hgrid] with ω hω
  have hp := gridTime_path_limit (τ ω) (fun t => X t ω) (hr ω (τ ω))
  exact hp.congr (fun n => hω n)

/-- The whole arbitrary-stopping-time identity. The terminal CE representation
 follows from the given martingale property rather than being postulated. -/
theorem continuous_optional_sampling_written {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] {T : EReal} (hT : 0 ≤ T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (X : ClosedTime T → Ω → ℝ) (hX : ∀ t, Measurable[F t] (X t))
    (hi : ∀ t, Integrable (X t) P)
    (hr : ∀ ω t, ContinuousWithinAt (fun s => X s ω) (Ici t) t)
    (hmart : ∀ s t, s ≤ t → P[X t | F s] =ᵐ[P] X s)
    (τ σ : Ω → ClosedTime T)
    (hτ : ∀ t, MeasurableSet[F t] {ω | τ ω ≤ t})
    (hσ : ∀ t, MeasurableSet[F t] {ω | σ ω ≤ t}) :
    P[(fun ω => X (τ ω) ω) | writtenStoppedSpace m F σ hσ] =ᵐ[P]
      (fun ω => X (min (τ ω) (σ ω)) ω) := by
  let topTime : ClosedTime T := ⟨T,hT,le_rfl⟩
  have hc (t : ClosedTime T) : X t =ᵐ[P] P[X topTime | F t] :=
    (hmart t topTime t.property.2).symm
  have hmY := (hX topTime).mono (hle topTime) le_rfl
  have hmin := (written_stopping_min_max F τ σ hτ hσ).1
  have ht := continuous_closed_optional_written P hT F hF hle τ hτ X hX hr hmY (hi topTime) hc
  have hminval := continuous_closed_optional_written P hT F hF hle
    (fun ω => min (τ ω) (σ ω)) hmin X hX hr hmY (hi topTime) hc
  have hcomm := written_asano_commute (P := P) (Icc 0 T) F hF hle σ τ hσ hτ (hi topTime)
  have heq := written_stopped_min_sigma m F τ σ hτ hσ
  rw [heq,inf_comm] at hminval
  exact (condExp_congr_ae ht).trans (hcomm.trans hminval.symm)

end Asakura.FullAudit

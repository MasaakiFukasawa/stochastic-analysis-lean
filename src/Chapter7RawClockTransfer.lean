import Chapter7RandomTimeRawLocal
import Chapter7ClockHalfTime
import Chapter6LocalFromStopped
import Chapter2LocalPathEncoding

open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false

/-- Transfer an actual local martingale through a clock. The inverse-time
stopping events and deterministic clock identities are separate inputs;
new localizers, optional sampling, and the
local-martingale conclusion are all constructed here. -/
theorem local_martingale_raw_clock_transfer
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)]
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t ≤ m)
    (X : ClosedTime T → Ω → ℝ) (hX : LocalMProcessWitness P F X)
    (τ : ℝ → Ω → ClosedTime T) (hτ : ∀ s t,MeasurableSet[F t] {w | τ s w ≤ t})
    (hm : ∀ w,Monotone (fun s => τ s w)) (hz : ∀ w,τ 0 w = ⊥)
    (hτt : ∀ r w,τ r w < ⊤)
    (hBc : ∀ w,Continuous (fun s => X (τ s w) w))
    (C : ClosedTime T → Ω → ℝ)
    (hCn : ∀ w a,a < ⊤ → 0 ≤ C a w)
    (hCm : ∀ w,MonotoneOn (fun a => C a w) (Iio ⊤))
    (hCu : ∀ w r,∃ a,a < ⊤ ∧ r < C a w)
    (hstop : ∀ w a,a < ⊤ → ∀ r,
      X (min a (τ r w)) w = X (τ (min (C a w) r) w) w) :
    let G := fun s : ℝ≥0 => writtenStoppedSpace m F (τ s) (hτ s)
    LocalMProcessWitness P (halfClosedFiltration m G)
      (fun t w => X (τ (halfTimeReal t) w) w) := by
  obtain ⟨ρ,hρ,hρm,hρt,hρco,hρB⟩ := hX.localizers
  let H := fun r => writtenStoppedSpace m F (τ r) (hτ r)
  let G := fun s : ℝ≥0 => H s
  let G' := halfClosedFiltration m G
  let Y := fun (t : HalfClosedTime) w => X (τ (halfTimeReal t) w) w
  let σ := fun n w => realTimeClamp (T := (⊤:EReal)) (C (ρ n w) w)
  have hHm : Monotone H := fun a b hab => written_stoppedSpace_mono m F
    (τ a) (τ b) (hτ a) (hτ b) (fun w => hm w hab)
  have hGm : Monotone G := fun s t hst => hHm hst
  have hGl s : G s ≤ m := fun _ he => he.1
  have hYm (r : ℝ) : Measurable[H r] (fun w => X (τ r w) w) := by
    apply @glued_value_measurable Ω (H r)
      (fun n w => X (min (ρ n w) (τ r w)) w)
      (fun n => random_time_adapted (Fact.out : 0 ≤ T) F hF hle _
        (hρB n).1.adapted (hρB n).1.path τ hτ r)
    intro w
    obtain ⟨n,hn⟩ := hρco w (τ r w) (hτt r w)
    exact eventually_atTop.mpr ⟨n,fun k hk => by rw [min_eq_right (hn.le.trans (hρm w hk))]⟩
  have hYa t : Measurable[G' t] (Y t) := by
    apply (hYm _).mono _ le_rfl
    by_cases ht : t < ⊤
    · simpa only [G',halfClosedFiltration,if_pos ht] using
        (show H (halfTimeReal t) ≤ G (halfTimeReal t) from le_rfl)
    · simpa only [G',halfClosedFiltration,if_neg ht] using
        (show H (halfTimeReal t) ≤ m from fun _ he => he.1)
  have hYc w t (ht : t < ⊤) : ContinuousAt (fun s => Y s w) t :=
    (hBc w).continuousAt.comp (changed_time_coordinate_continuousAt t ht)
  have hY0 : Y ⊥ =ᵐ[P] 0 := by
    change (fun w => X (τ 0 w) w) =ᵐ[P] 0
    simpa only [hz] using hX.initial P F
  apply Asakura.Chapter6.local_of_local_stopped P (show (0:EReal) < ⊤ by simp) G'
    (half_closed_filtration_mono m G hGm hGl) (half_closed_filtration_le m G hGl) Y hYa hYc hY0 σ
  · intro w n k hnk
    exact real_time_clamp_mono (hCm w (hρt n w) (hρt k w) (hρm w hnk))
  · intro w
    apply changed_time_cofinal _ (fun n => hCn w _ (hρt n w))
    intro r
    obtain ⟨a,ha,hr⟩ := hCu w r
    obtain ⟨n,hn⟩ := hρco w a ha
    exact ⟨n,hr.trans_le (hCm w ha (hρt n w) hn.le)⟩
  · intro n
    have hsc w : Continuous (fun r => X (min (ρ n w) (τ r w)) w) := by
      have he : (fun r => X (min (ρ n w) (τ r w)) w) =
          fun r => X (τ (min (C (ρ n w) w) r) w) w := funext (hstop w _ (hρt n w))
      rw [he]
      exact (hBc w).comp (continuous_const.min continuous_id)
    have hl := random_time_raw_closed_martingale_local P F hF hle _ (hρB n).1 τ hτ hm hz hsc
    apply hl.congr_before_terminal P G'
    intro t ht
    funext w
    change X (min (ρ n w) (τ (halfTimeReal t) w)) w = Y (min (σ n w) t) w
    rw [hstop w _ (hρt n w)]
    dsimp only [Y,σ]
    rw [changed_time_min_real _ (hCn w _ (hρt n w)) t ht]

end Asakura.Chapter7

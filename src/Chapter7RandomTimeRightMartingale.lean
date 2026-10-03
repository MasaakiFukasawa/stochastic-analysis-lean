import Chapter7RandomTimeSampling
import Chapter7RightClockStopping

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- Optional sampling followed by backward conditional-expectation
convergence proves the martingale identity for the right-continuous changed
filtration. The changed martingale identity is not an input. -/
theorem random_time_right_martingale_identity
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} (hT : 0 ≤ T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t ≤ m)
    (X : ClosedTime T → Ω → ℝ) (ha : ∀ t,Measurable[F t] (X t))
    (hi : ∀ t,Integrable (X t) P) (hc : ∀ w,Continuous (fun t => X t w))
    (hM : ∀ s t,s ≤ t → P[X t|F s] =ᵐ[P] X s)
    (K : ℝ) (hb : ∀ᵐ w ∂P,∀ t,|X t w| ≤ K)
    (τ : ℝ → Ω → ClosedTime T) (hτ : ∀ s t,MeasurableSet[F t] {w | τ s w ≤ t})
    (hm : ∀ w,Monotone (fun s => τ s w))
    (hBc : ∀ w,Continuous (fun s => X (τ s w) w))
    (s t : ℝ) (hst : s < t) :
    P[(fun w => X (τ t w) w)|⨅ r : Ioi s,writtenStoppedSpace m F (τ r.val) (hτ r.val)] =ᵐ[P]
      (fun w => X (τ s w) w) := by
  let H := fun r => writtenStoppedSpace m F (τ r) (hτ r)
  have hHm : Monotone H := fun a b hab => written_stoppedSpace_mono m F
    (τ a) (τ b) (hτ a) (hτ b) (fun w => hm w hab)
  have hHl r : H r ≤ m := fun _ he => he.1
  have hB r : Measurable[m] (fun w => X (τ r w) w) :=
    (random_time_adapted hT F hF hle X ha hc τ hτ r).mono (hHl r) le_rfl
  have hBi r : Integrable (fun w => X (τ r w) w) P :=
    Integrable.of_bound (hB r).aestronglyMeasurable K (hb.mono fun w hw => by
      simpa only [Real.norm_eq_abs] using hw (τ r w))
  let u := fun n : ℕ => s+(t-s)/(n+2:ℝ)
  have hu n : s < u n ∧ u n < t := by
    have hd : 0 < (n+2:ℝ) := by positivity
    have hd1 : 1 < (n+2:ℝ) := by have hn := Nat.cast_nonneg (α := ℝ) n; linarith
    have hdiv := div_lt_self (sub_pos.mpr hst) hd1
    exact ⟨lt_add_of_pos_right s (div_pos (sub_pos.mpr hst) hd),by dsimp [u]; linarith⟩
  have hum : Antitone u := by
    intro n k hnk
    apply add_le_add_right
    exact div_le_div_of_nonneg_left (sub_nonneg.mpr hst.le) (by positivity)
      (by exact_mod_cast Nat.add_le_add_right hnk 2)
  have hul : Tendsto u atTop (𝓝 s) := by
    have hh := ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 1)).const_mul (t-s)
    convert (tendsto_const_nhds (x := s)).add hh using 1 <;> simp [u,div_eq_mul_inv,Nat.cast_add] <;> ring
  have he := time_changed_right_filtration_identity P (fun n => H (u n))
    (fun n k hnk => hHm (hum hnk)) (fun n => hHl (u n))
    (fun r w => X (τ r w) w) hBc s u hul (fun w => X (τ t w) w) (hB t) (hBi t) (hB s)
    (fun n => random_time_martingale_identity P hT F hF hle X ha hi hc hM τ hτ hm
      (u n) t (hu n).2.le)
  rwa [right_filtration_countable_intersection H hHm s u (fun n => (hu n).1) hul] at he

end Asakura.Chapter7

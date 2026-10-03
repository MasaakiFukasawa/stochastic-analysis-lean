import Chapter7RandomTimeRightMartingale

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- The terminal conditional representation after the change of clock. It
also treats a new time horizon equal to infinity: the terminal random
variable is the original stopped value, never X at the unused endpoint. -/
theorem random_time_right_terminal_identity
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 ≤ T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t ≤ m)
    (X : ClosedTime T → Ω → ℝ) (ha : ∀ t,Measurable[F t] (X t))
    (hi : ∀ t,Integrable (X t) P) (hc : ∀ w,Continuous (fun t => X t w))
    (hM : ∀ s t,s ≤ t → P[X t|F s] =ᵐ[P] X s)
    (τ : ℝ → Ω → ClosedTime T) (hτ : ∀ s t,MeasurableSet[F t] {w | τ s w ≤ t})
    (hm : ∀ w,Monotone (fun s => τ s w))
    (hBc : ∀ w,Continuous (fun s => X (τ s w) w)) (s : ℝ) :
    P[X ⊤|⨅ r : Ioi s,writtenStoppedSpace m F (τ r.val) (hτ r.val)] =ᵐ[P]
      (fun w => X (τ s w) w) := by
  let H := fun r => writtenStoppedSpace m F (τ r) (hτ r)
  have hHm : Monotone H := fun a b hab => written_stoppedSpace_mono m F
    (τ a) (τ b) (hτ a) (hτ b) (fun w => hm w hab)
  have hHl r : H r ≤ m := fun _ he => he.1
  have hB r : Measurable[m] (fun w => X (τ r w) w) :=
    (random_time_adapted hT F hF hle X ha hc τ hτ r).mono (hHl r) le_rfl
  let u := fun n : ℕ => s+1/(n+1:ℝ)
  have hu n : s < u n := lt_add_of_pos_right s (by positivity)
  have hum : Antitone u := by
    intro n k hnk
    apply add_le_add_right
    exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hnk 1)
  have hul : Tendsto u atTop (𝓝 s) := by
    simpa only [add_zero] using (tendsto_const_nhds (x := s)).add
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have he n : P[X ⊤|H (u n)] =ᵐ[P] (fun w => X (τ (u n) w) w) := by
    exact (continuous_closed_optional_written P hT F hF hle (τ (u n)) (hτ (u n)) X ha
      (fun w t => (hc w).continuousAt.continuousWithinAt)
      ((ha ⊤).mono (hle ⊤) le_rfl) (hi ⊤)
      (fun t => (hM t ⊤ le_top).symm)).symm
  have hh := time_changed_right_filtration_identity P (fun n => H (u n))
    (fun n k hnk => hHm (hum hnk)) (fun n => hHl (u n))
    (fun r w => X (τ r w) w) hBc s u hul (X ⊤) ((ha ⊤).mono (hle ⊤) le_rfl) (hi ⊤) (hB s) he
  rwa [right_filtration_countable_intersection H hHm s u hu hul] at hh

end Asakura.Chapter7

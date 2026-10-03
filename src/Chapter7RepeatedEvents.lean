import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Analysis.SpecificLimits.Basic

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter7
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- The elementary conditional iteration used in the occupation proof.
The event at stage j is observable before stage j+1; no independence of
all the events is assumed. -/
theorem repeated_events_infinitely_often
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (F : ℕ → MeasurableSpace Ω) (hF : Monotone F)
    (A : ℕ → Set Ω) (hA : ∀ j,MeasurableSet[F (j+1)] (A j))
    (q : ℝ≥0∞) (hq : q < 1)
    (hcut : ∀ j E,MeasurableSet[F j] E → P (E ∩ (A j)ᶜ) ≤ q*P E) :
    ∀ᵐ w ∂P,∀ N : ℕ,∃ j,N ≤ j ∧ w ∈ A j := by
  apply ae_all_iff.mpr
  intro N
  let B : ℕ → Set Ω := fun n => ⋂ k ∈ Finset.range n,(A (N+k))ᶜ
  have hB0 : B 0 = univ := by simp [B]
  have hBs n : B (n+1) = B n ∩ (A (N+n))ᶜ := by
    ext w
    simp only [B,mem_iInter,Finset.mem_range,mem_inter_iff]
    constructor
    · intro h
      exact ⟨fun k hk => h k (Nat.lt_succ_of_lt hk),h n (Nat.lt_succ_self n)⟩
    · rintro ⟨h,hn⟩ k hk
      rcases lt_or_eq_of_le (Nat.le_of_lt_succ hk) with hk | rfl
      · exact h k hk
      · exact hn
  have hBm n : MeasurableSet[F (N+n)] (B n) := by
    induction n with
    | zero => simpa only [hB0] using (MeasurableSet.univ : MeasurableSet[F (N+0)] univ)
    | succ n ih =>
      rw [hBs]
      apply ((hF (by omega)) _ ih).inter
      simpa only [Nat.add_assoc] using (hA (N+n)).compl
  have hb n : P (B n) ≤ q^n := by
    induction n with
    | zero => simp only [hB0,measure_univ,pow_zero,le_refl]
    | succ n ih =>
      rw [hBs,pow_succ']
      exact (hcut (N+n) (B n) (hBm n)).trans (mul_le_mul' le_rfl ih)
  have he n : {w | ¬∃ j,N ≤ j ∧ w ∈ A j} ⊆ B n := by
    intro w hw
    simp only [B,mem_iInter,mem_compl_iff]
    intro k _
    exact fun hk => hw ⟨N+k,Nat.le_add_right _ _,hk⟩
  apply ae_iff.mpr
  apply le_antisymm _ bot_le
  apply ge_of_tendsto (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hq)
  exact Eventually.of_forall fun n => (measure_mono (he n)).trans (hb n)

end Asakura.Chapter7

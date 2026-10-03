import Chapter7BrownianAllLevels

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 2200000

/-- There is one event of probability one on which every level is reached
after every finite time. In particular the recursively defined returns
in the occupation proof are all finite. -/
theorem brownian_future_levels
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (B : BrownianSystem P 1) :
    ∀ᵐ w ∂P,∀ a x : ℝ,∃ r : ℝ,0 ≤ r ∧ a ≤ r ∧ B.W 0 (realTimeClamp r) w = x := by
  have hn (n : ℕ) := brownian_all_levels P (B.shift n (Nat.cast_nonneg n))
  filter_upwards [ae_all_iff.mpr hn] with w hw
  intro a x
  obtain ⟨n,han⟩ := exists_nat_gt a
  obtain ⟨r,hr,he⟩ := hw n (x-B.W 0 (realTimeClamp (n:ℝ)) w)
  change B.W 0 (deterministicTimeShift (n:ℝ) (Nat.cast_nonneg n) (realTimeClamp r)) w-
    B.W 0 (deterministicTimeShift (n:ℝ) (Nat.cast_nonneg n) ⊥) w = _ at he
  rw [deterministic_shift_real _ _ r hr,deterministic_shift_bot] at he
  exact ⟨n+r,add_nonneg (Nat.cast_nonneg n) hr,by linarith,by linarith⟩

end Asakura.Chapter7

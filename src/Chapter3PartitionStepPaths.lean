import Chapter3OscillationPartitionFormula

open MeasureTheory Set Filter
open scoped Topology BigOperators
namespace Asakura.Chapter3Complete
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

/-- The predictable step coefficient used in the discrete Ito sum. -/
noncomputable def partitionStep {ι : Type*} [LinearOrder ι]
    (H : ι → ℝ) (τ : ℕ → ι) (t : ι) : ℝ :=
  ∑' j, (Ioc (τ j) (τ (j+1))).indicator (fun _ => H (τ j)) t

/-- Every positive finite time belongs to a partition interval, even if
some consecutive stopping times coincide. -/
theorem partition_interval_index
    {ι : Type*} [LinearOrder ι] [BoundedOrder ι]
    (τ : ℕ → ι) (h0 : τ 0 = ⊥)
    (hco : ∀ t, t < ⊤ → ∃ N, t < τ N)
    (t : ι) (ht0 : ⊥ < t) (htt : t < ⊤) :
    ∃ j, t ∈ Ioc (τ j) (τ (j+1)) := by
  have hex : ∃ N, t ≤ τ N := by obtain ⟨N,hN⟩ := hco t htt; exact ⟨N,hN.le⟩
  let N := Nat.find hex
  have hNt : t ≤ τ N := Nat.find_spec hex
  have hN0 : N ≠ 0 := by
    intro h
    rw [h,h0] at hNt
    exact not_le_of_gt ht0 hNt
  obtain ⟨j,hj⟩ := Nat.exists_eq_succ_of_ne_zero hN0
  refine ⟨j,?_,?_⟩
  · apply lt_of_not_ge
    intro htj
    exact Nat.find_min hex (by omega : j < N) htj
  · simpa only [hj,Nat.succ_eq_add_one] using hNt

theorem partition_interval_unique
    {ι : Type*} [LinearOrder ι] (τ : ℕ → ι) (hτ : Monotone τ)
    (t : ι) {i j : ℕ} (hi : t ∈ Ioc (τ i) (τ (i+1))) (hj : t ∈ Ioc (τ j) (τ (j+1))) : i = j := by
  rcases lt_trichotomy i j with h | h | h
  · exact False.elim ((not_le_of_gt hj.1) (hi.2.trans (hτ (by omega))))
  · exact h
  · exact False.elim ((not_le_of_gt hi.1) (hj.2.trans (hτ (by omega))))

theorem partition_step_value
    {ι : Type*} [LinearOrder ι] (H : ι → ℝ) (τ : ℕ → ι) (hτ : Monotone τ)
    (t : ι) (j : ℕ) (hj : t ∈ Ioc (τ j) (τ (j+1))) : partitionStep H τ t = H (τ j) := by
  unfold partitionStep
  rw [tsum_eq_single j]
  · exact indicator_of_mem hj _
  · intro i hi
    apply indicator_of_notMem
    intro hm
    exact hi (partition_interval_unique τ hτ t hm hj)

/-- The step approximation has the manuscript's pointwise oscillation
error at every positive finite time. -/
theorem partition_step_error
    {ι : Type*} [LinearOrder ι] [BoundedOrder ι]
    (H : ι → ℝ) (τ : ℕ → ι) (hτ : Monotone τ) (h0 : τ 0 = ⊥)
    (hco : ∀ t, t < ⊤ → ∃ N, t < τ N) (δ : ℝ)
    (hosc : ∀ j t, τ j ≤ t → t ≤ τ (j+1) → |H (τ j)-H t| ≤ δ)
    (t : ι) (ht0 : ⊥ < t) (htt : t < ⊤) : |partitionStep H τ t-H t| ≤ δ := by
  obtain ⟨j,hj⟩ := partition_interval_index τ h0 hco t ht0 htt
  rw [partition_step_value H τ hτ t j hj]
  exact hosc j t hj.1.le hj.2

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.partition_interval_index
#print axioms Asakura.Chapter3Complete.partition_interval_unique
#print axioms Asakura.Chapter3Complete.partition_step_value
#print axioms Asakura.Chapter3Complete.partition_step_error

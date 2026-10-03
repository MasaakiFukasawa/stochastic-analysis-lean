import Chapter3SignedStieltjesApproximation

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

theorem linear_partition_sum_add
    {T : EReal} [Fact (0 ≤ T)] (U V A H : ClosedTime T → ℝ)
    (τ : ℕ → ClosedTime T) (hτ : Monotone τ)
    (b : ClosedTime T) (hb : b < ⊤) (hco : ∀ t, t < ⊤ → ∃ N, t < τ N)
    (he : ∀ s, s ≤ b → A s = U s+V s) (t : ClosedTime T) :
    (∑' j, H (τ j)*(A (min (τ (j+1)) (min b t))-A (min (τ j) (min b t)))) =
      (∑' j, H (τ j)*(U (min (τ (j+1)) (min b t))-U (min (τ j) (min b t))))+
      (∑' j, H (τ j)*(V (min (τ (j+1)) (min b t))-V (min (τ j) (min b t)))) := by
  obtain ⟨N,hN⟩ := hco b hb
  rw [partition_sum_truncates_before_endpoint τ hτ A (fun j => H (τ j)) N _ ((min_le_left _ _).trans hN.le),
    partition_sum_truncates_before_endpoint τ hτ U (fun j => H (τ j)) N _ ((min_le_left _ _).trans hN.le),
    partition_sum_truncates_before_endpoint τ hτ V (fun j => H (τ j)) N _ ((min_le_left _ _).trans hN.le),
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  rw [he _ ((min_le_right _ _).trans (min_le_left _ _)),he _ ((min_le_right _ _).trans (min_le_left _ _))]
  ring

theorem uniform_limit_add
    {ι : Type*} (U V : ℕ → ι → ℝ) (u v : ι → ℝ)
    (hU : TendstoUniformly U u atTop) (hV : TendstoUniformly V v atTop) :
    TendstoUniformly (fun n t => U n t+V n t) (fun t => u t+v t) atTop := by
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  filter_upwards [Metric.tendstoUniformly_iff.mp hU (ε/2) (half_pos hε),
    Metric.tendstoUniformly_iff.mp hV (ε/2) (half_pos hε)] with n hu hv
  intro t
  have hu' : |u t-U n t| < ε/2 := by simpa only [Real.dist_eq] using hu t
  have hv' : |v t-V n t| < ε/2 := by simpa only [Real.dist_eq] using hv t
  have h := (abs_add_le (u t-U n t) (v t-V n t)).trans_lt (add_lt_add hu' hv')
  have he : (u t-U n t)+(v t-V n t) = (u t+v t)-(U n t+V n t) := by ring
  rw [he,add_halves] at h
  simpa only [Real.dist_eq] using h

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.linear_partition_sum_add
#print axioms Asakura.Chapter3Complete.uniform_limit_add

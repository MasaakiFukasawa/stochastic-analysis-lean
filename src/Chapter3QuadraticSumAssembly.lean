import Chapter3DiscreteQVErrorConvergence
import Chapter3StoppedStieltjesApproximation

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

/-- Exact decomposition of the locally finite quadratic sum into the
square-defect sum and the Stieltjes sum. Infinite-series subtraction is
justified from cofinality, not assumed. -/
theorem partition_quadratic_sum_decomposition
    {ι : Type*} [LinearOrder ι] [OrderTop ι]
    (τ : ℕ → ι) (hτ : Monotone τ)
    (hcofinal : ∀ b, b < ⊤ → ∃ N, b < τ N)
    (X Q : ι → ℝ) (A : ℕ → ℝ) (b t : ι) (hb : b < ⊤) (ht : t ≤ b) :
    (∑' j, A j*(X (min (τ (j+1)) t)-X (min (τ j) t))^2) =
    (∑' j, A j*((X (min (τ (j+1)) t)-X (min (τ j) t))^2-
      (Q (min (τ (j+1)) t)-Q (min (τ j) t))))+
    (∑' j, A j*(Q (min (τ (j+1)) t)-Q (min (τ j) t))) := by
  obtain ⟨N,hN⟩ := hcofinal b hb
  have hz (j : ℕ) (hj : j ∉ Finset.range N) (Z : ι → ℝ) :
      Z (min (τ (j+1)) t)-Z (min (τ j) t) = 0 := by
    have hNj := Nat.le_of_not_gt (fun h => hj (Finset.mem_range.mpr h))
    have hjt : t ≤ τ j := ht.trans (hN.le.trans (hτ hNj))
    rw [min_eq_right hjt,min_eq_right (hjt.trans (hτ (Nat.le_succ j))),sub_self]
  have hs : (∑' j, A j*(X (min (τ (j+1)) t)-X (min (τ j) t))^2) =
      ∑ j ∈ Finset.range N, A j*(X (min (τ (j+1)) t)-X (min (τ j) t))^2 := by
    apply tsum_eq_sum
    intro j hj
    rw [hz j hj X,zero_pow (by decide : 2 ≠ 0),mul_zero]
  have he : (∑' j, A j*((X (min (τ (j+1)) t)-X (min (τ j) t))^2-
      (Q (min (τ (j+1)) t)-Q (min (τ j) t)))) =
      ∑ j ∈ Finset.range N, A j*((X (min (τ (j+1)) t)-X (min (τ j) t))^2-
      (Q (min (τ (j+1)) t)-Q (min (τ j) t))) := by
    apply tsum_eq_sum
    intro j hj
    rw [hz j hj X,hz j hj Q,zero_pow (by decide : 2 ≠ 0),sub_self,mul_zero]
  have hq : (∑' j, A j*(Q (min (τ (j+1)) t)-Q (min (τ j) t))) =
      ∑ j ∈ Finset.range N, A j*(Q (min (τ (j+1)) t)-Q (min (τ j) t)) := by
    apply tsum_eq_sum
    intro j hj
    rw [hz j hj Q,mul_zero]
  rw [hs,he,hq,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The continuous-path norm convergence supplied by the stochastic
estimate is precisely the uniform error needed to add the Stieltjes limit. -/
theorem uniform_limit_of_continuous_path_error
    {ι : Type*} [TopologicalSpace ι] [CompactSpace ι]
    (E : ℕ → C(ι,ℝ)) (R : ℕ → ι → ℝ) (I : ι → ℝ)
    (hE : Tendsto E atTop (𝓝 0)) (hR : TendstoUniformly R I atTop) :
    TendstoUniformly (fun n t => E n t+R n t) I atTop := by
  have hn : Tendsto (fun n => ‖E n‖) atTop (𝓝 0) := by simpa using hE.norm
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  have hε2 : 0 < ε/2 := half_pos hε
  filter_upwards [hn.eventually (gt_mem_nhds hε2),
    Metric.tendstoUniformly_iff.mp hR (ε/2) hε2] with n hn hr
  intro t
  have hb : |E n t| ≤ ‖E n‖ := by
    simpa only [Real.norm_eq_abs] using (E n).norm_coe_le_norm t
  have he : |E n t| < ε/2 := hb.trans_lt hn
  have hi : |R n t-I t| < ε/2 := by simpa only [Real.dist_eq,abs_sub_comm] using hr t
  have hh := (abs_add_le (E n t) (R n t-I t)).trans_lt (add_lt_add he hi)
  rw [← add_sub_assoc] at hh
  simpa only [Real.dist_eq,abs_sub_comm,add_halves] using hh

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.partition_quadratic_sum_decomposition
#print axioms Asakura.Chapter3Complete.uniform_limit_of_continuous_path_error

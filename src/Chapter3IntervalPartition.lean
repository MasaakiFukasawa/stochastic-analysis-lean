import Chapter3FinitePartitionIntegral

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter3Complete
set_option maxHeartbeats 800000

/-- The intervals (u_j,u_(j+1)] cover (u_0,u_N], even when grid points repeat. -/
theorem interval_partition_cover (u : ℕ → ℝ) (N : ℕ) (x : ℝ)
    (hx : x ∈ Ioc (u 0) (u N)) :
    ∃ j ∈ Finset.range N, x ∈ Ioc (u j) (u (j+1)) := by
  induction N with
  | zero => exact (not_lt_of_ge hx.2 hx.1).elim
  | succ N ih =>
    by_cases h : x ≤ u N
    · obtain ⟨j,hj,hxj⟩ := ih ⟨hx.1,h⟩
      exact ⟨j,Finset.mem_range.mpr ((Finset.mem_range.mp hj).trans (Nat.lt_succ_self N)),hxj⟩
    · exact ⟨N,Finset.mem_range.mpr (Nat.lt_succ_self N),lt_of_not_ge h,hx.2⟩

theorem interval_partition_disjoint (u : ℕ → ℝ) (hu : Monotone u)
    (i j : ℕ) (hij : i ≠ j) : Disjoint (Ioc (u i) (u (i+1))) (Ioc (u j) (u (j+1))) := by
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  rcases lt_or_gt_of_ne hij with h | h
  · exact (not_lt_of_ge (hxi.2.trans (hu (Nat.succ_le_of_lt h)))) hxj.1
  · exact (not_lt_of_ge (hxj.2.trans (hu (Nat.succ_le_of_lt h)))) hxi.1

/-- The deterministic Riemann--Stieltjes error used in prop:qcv, stated for
the actual finite measure. The step integral is evaluated as interval masses;
all cumulative errors are bounded simultaneously by δ times total mass. -/
theorem interval_partition_cumulative_error
    (μ : Measure ℝ) [IsFiniteMeasure μ] (u : ℕ → ℝ) (hu : Monotone u) (N : ℕ)
    (hμ : ∀ᵐ x ∂μ, x ∈ Ioc (u 0) (u N))
    (H : ℝ → ℝ) (hH : AEStronglyMeasurable H μ)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hosc : ∀ j ∈ Finset.range N, ∀ x ∈ Ioc (u j) (u (j+1)), |H (u j)-H x| ≤ δ) :
    Integrable H μ ∧ ∀ t : ℝ,
      |(∑ j ∈ Finset.range N, H (u j)*μ.real (Iic t ∩ Ioc (u j) (u (j+1))))-
        (∫ x in Iic t, H x ∂μ)| ≤ δ*μ.real univ := by
  obtain ⟨hi,hbound⟩ := finite_partition_cumulative_error μ (Finset.range N)
    (fun j => Ioc (u j) (u (j+1))) (fun _ _ => measurableSet_Ioc)
    (fun j => H (u j)) H hH
    (fun i _ j _ hij => interval_partition_disjoint u hu i j hij)
    (hμ.mono fun x hx => interval_partition_cover u N x hx) δ hδ hosc
  refine ⟨hi,?_⟩
  intro t
  have he : (∫ x in Iic t, (∑ j ∈ Finset.range N,
      (Ioc (u j) (u (j+1))).indicator (fun _ => H (u j)) x) ∂μ) =
      ∑ j ∈ Finset.range N, H (u j)*μ.real (Iic t ∩ Ioc (u j) (u (j+1))) := by
    rw [integral_finsetSum _ (fun j _ => (integrable_const _).indicator measurableSet_Ioc)]
    apply Finset.sum_congr rfl
    intro j hj
    rw [setIntegral_indicator measurableSet_Ioc,setIntegral_const,smul_eq_mul]
    rw [inter_comm]
    ring
  simpa only [he] using hbound (Iic t) measurableSet_Iic

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.interval_partition_cover
#print axioms Asakura.Chapter3Complete.interval_partition_disjoint
#print axioms Asakura.Chapter3Complete.interval_partition_cumulative_error

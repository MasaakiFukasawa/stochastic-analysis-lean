import Chapter3IntervalPartition

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter3Complete
set_option maxHeartbeats 1000000

/-- Evaluate the mass of a partition interval cut off at t, including the
case in which that interval has not started yet. -/
theorem cumulative_interval_mass
    (μ : Measure ℝ) (Q : ℝ → ℝ)
    (hmass : ∀ a b, a ≤ b → μ.real (Ioc a b) = Q b-Q a)
    (a b t : ℝ) (hab : a ≤ b) :
    μ.real (Iic t ∩ Ioc a b) = Q (min b t)-Q (min a t) := by
  by_cases hat : a ≤ t
  · have he : Iic t ∩ Ioc a b = Ioc a (min b t) := by
      ext x
      simp only [mem_inter_iff,mem_Iic,mem_Ioc,le_min_iff]
      tauto
    rw [he,hmass a (min b t) (le_min hab hat),min_eq_left hat]
  · have hta : t < a := lt_of_not_ge hat
    have he : Iic t ∩ Ioc a b = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact (not_lt_of_ge (hx.1.trans hta.le)) hx.2.1
    simp only [he,Measure.real,measure_empty,ENNReal.toReal_zero,min_eq_right hta.le,min_eq_right (hta.le.trans hab),sub_self]

/-- The deterministic Stieltjes error exactly as used in prop:qcv, for a
finite localized Stieltjes measure and an oscillation-controlled partition.
The defining interval-mass formula is explicit and is satisfied by the
Stieltjes measures constructed in the appendix/chapter 2. -/
theorem stieltjes_riemann_error
    (μ : Measure ℝ) [IsFiniteMeasure μ] (Q H : ℝ → ℝ)
    (hmass : ∀ a b, a ≤ b → μ.real (Ioc a b) = Q b-Q a)
    (u : ℕ → ℝ) (hu : Monotone u) (N : ℕ)
    (hsupport : ∀ᵐ x ∂μ, x ∈ Ioc (u 0) (u N))
    (hH : AEStronglyMeasurable H μ)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hosc : ∀ j ∈ Finset.range N, ∀ x ∈ Ioc (u j) (u (j+1)), |H (u j)-H x| ≤ δ) :
    Integrable H μ ∧ ∀ t,
      |(∑ j ∈ Finset.range N, H (u j)*(Q (min (u (j+1)) t)-Q (min (u j) t)))-
        (∫ x in Iic t, H x ∂μ)| ≤ δ*μ.real univ := by
  obtain ⟨hi,hb⟩ := interval_partition_cumulative_error μ u hu N hsupport H hH δ hδ hosc
  refine ⟨hi,?_⟩
  intro t
  simpa only [fun j => cumulative_interval_mass μ Q hmass (u j) (u (j+1)) t (hu (Nat.le_succ j))]
    using hb t

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.cumulative_interval_mass
#print axioms Asakura.Chapter3Complete.stieltjes_riemann_error

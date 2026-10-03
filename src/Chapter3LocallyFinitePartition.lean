import Chapter3WrittenLimits

open Set Filter
open scoped Topology BigOperators
namespace Asakura.Chapter3Complete

/-- A cofinal increasing stopping partition has only finitely many active
intervals on each compact time interval, path by path. The bound N can depend
on the path, but works simultaneously for every time up to b. -/
theorem partition_increment_finite_support
    {ι : Type*} [LinearOrder ι] [OrderTop ι]
    (τ : ℕ → ι) (hτ : Monotone τ)
    (hcofinal : ∀ b, b < ⊤ → ∃ N, b < τ N)
    (X : ι → ℝ) (b : ι) (hb : b < ⊤) :
    ∃ N, ∀ j, N ≤ j → ∀ t, t ≤ b →
      X (min (τ (j+1)) t)-X (min (τ j) t) = 0 := by
  obtain ⟨N,hN⟩ := hcofinal b hb
  refine ⟨N,?_⟩
  intro j hj t ht
  have hjt : t ≤ τ j := ht.trans (hN.le.trans (hτ hj))
  simp only [min_eq_right hjt,min_eq_right (hjt.trans (hτ (Nat.le_succ j))),sub_self]

/-- The infinite weighted Riemann sum is exactly a finite sum, uniformly on
a fixed compact time interval. Thus no pathwise convergence of an infinite
series needs to be postulated in the discrete Ito approximation. -/
theorem partition_riemann_sum_locally_finite
    {ι : Type*} [LinearOrder ι] [OrderTop ι]
    (τ : ℕ → ι) (hτ : Monotone τ)
    (hcofinal : ∀ b, b < ⊤ → ∃ N, b < τ N)
    (X : ι → ℝ) (A : ℕ → ℝ) (b : ι) (hb : b < ⊤) :
    ∃ N, ∀ k, N ≤ k → ∀ t, t ≤ b →
      (∑' j, A j*(X (min (τ (j+1)) t)-X (min (τ j) t))) =
        ∑ j ∈ Finset.range k, A j*(X (min (τ (j+1)) t)-X (min (τ j) t)) := by
  obtain ⟨N,hN⟩ := partition_increment_finite_support τ hτ hcofinal X b hb
  refine ⟨N,?_⟩
  intro k hk t ht
  apply tsum_eq_sum
  intro j hj
  have hkj : k ≤ j := Nat.le_of_not_gt (fun h => hj (Finset.mem_range.mpr h))
  rw [hN j (hk.trans hkj) t ht,mul_zero]

/-- The same stabilization applies to square defects and weighted quadratic
variation sums, so the same truncation controls their difference. -/
theorem partition_defect_sum_locally_finite
    {ι : Type*} [LinearOrder ι] [OrderTop ι]
    (τ : ℕ → ι) (hτ : Monotone τ)
    (hcofinal : ∀ b, b < ⊤ → ∃ N, b < τ N)
    (X Q : ι → ℝ) (A : ℕ → ℝ) (b : ι) (hb : b < ⊤) :
    ∃ N, ∀ k, N ≤ k → ∀ t, t ≤ b →
      (∑' j, A j*((X (min (τ (j+1)) t)-X (min (τ j) t))^2-
        (Q (min (τ (j+1)) t)-Q (min (τ j) t)))) =
      ∑ j ∈ Finset.range k, A j*((X (min (τ (j+1)) t)-X (min (τ j) t))^2-
        (Q (min (τ (j+1)) t)-Q (min (τ j) t))) := by
  obtain ⟨N,hN⟩ := hcofinal b hb
  refine ⟨N,?_⟩
  intro k hk t ht
  apply tsum_eq_sum
  intro j hj
  have hkj : k ≤ j := Nat.le_of_not_gt (fun h => hj (Finset.mem_range.mpr h))
  have hjt : t ≤ τ j := ht.trans (hN.le.trans (hτ (hk.trans hkj)))
  simp only [min_eq_right hjt,min_eq_right (hjt.trans (hτ (Nat.le_succ j))),
    sub_self,zero_pow (by decide : 2 ≠ 0),mul_zero]

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.partition_increment_finite_support
#print axioms Asakura.Chapter3Complete.partition_riemann_sum_locally_finite
#print axioms Asakura.Chapter3Complete.partition_defect_sum_locally_finite

import Chapter3CovariationIntegralApproximation

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

/-- Recover a cumulative signed measure from its interval increments and
its constant lower tail. This identifies the unweighted quadratic sum. -/
theorem signed_cumulative_interval_identity (ν : SignedMeasure ℝ) (C : ℝ → ℝ)
    (hν : ∀ a b, a ≤ b → ν (Ioc a b) = C b-C a)
    (hC : ∀ a, a ≤ 0 → C a = C 0) (t : ℝ) (ht : 0 ≤ t) :
    signedIntegralRaw ν ((Iic t).indicator (fun _ => 1)) = C t-C 0 := by
  rw [signedIntegralRaw_indicator ν (Iic t) measurableSet_Iic]
  let S := fun n : ℕ => Ioc (-(n:ℝ)) t
  have hm : Monotone S := by
    intro n k hnk
    apply Ioc_subset_Ioc _ le_rfl
    exact neg_le_neg (by exact_mod_cast hnk)
  have he : (⋃ n, S n) = Iic t := by
    ext x
    constructor
    · rintro ⟨_,⟨n,rfl⟩,hx⟩
      exact hx.2
    · intro hx
      obtain ⟨n,hn⟩ := exists_nat_gt (-x)
      exact mem_iUnion.mpr ⟨n,by change -(n:ℝ) < x ∧ x ≤ t; exact ⟨by linarith,hx⟩⟩
  have hl := ν.tendsto_vectorMeasure_iUnion_atTop_nat hm (fun _ => measurableSet_Ioc)
  rw [he] at hl
  have hc n : ν (S n) = C t-C 0 := by
    change ν (Ioc (-(n:ℝ)) t) = C t-C 0
    rw [hν (-(n:ℝ)) t ((neg_nonpos.mpr (Nat.cast_nonneg n)).trans ht),
      hC (-(n:ℝ)) (neg_nonpos.mpr (Nat.cast_nonneg n))]
  simp_rw [hc] at hl
  exact tendsto_nhds_unique hl tendsto_const_nhds

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.signed_cumulative_interval_identity

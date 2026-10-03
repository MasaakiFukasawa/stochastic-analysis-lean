import Chapter3MomentHolder

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter3Complete
set_option maxHeartbeats 800000

/-- Cancellation of the moment factor in BDG, including the zero-moment case. -/
theorem fractional_moment_cancel {M N C a : ℝ}
    (hM : 0 ≤ M) (hN : 0 ≤ N) (hC : 0 ≤ C) (ha : 0 < a) (ha1 : a < 1)
    (h : M ≤ C*N^a*M^(1-a)) : M ≤ C^(1/a)*N := by
  rcases hM.eq_or_lt with h0 | hpos
  · rw [← h0]
    positivity
  have he : M = M^a*M^(1-a) := by
    rw [← Real.rpow_add hpos]
    simp
  have hh : M^a*M^(1-a) ≤ (C*N^a)*M^(1-a) := he.symm.trans_le h
  have hcanc := (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hpos (1-a))).mp hh
  have hpow := Real.rpow_le_rpow (Real.rpow_nonneg hM a) hcanc (by positivity : 0 ≤ 1/a)
  rw [← Real.rpow_mul hM,Real.mul_rpow hC (Real.rpow_nonneg hN a),← Real.rpow_mul hN] at hpow
  simpa [ha.ne'] using hpow

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.fractional_moment_cancel

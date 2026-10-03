import Chapter2CumulativeIntegral

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false

/-- The deterministic Cauchy-Schwarz estimate underlying the square
integrability of the finite-variation process in the density proof. -/
theorem cumulative_integral_square_bound
    (μ : Measure ℝ) [IsFiniteMeasure μ] (g : ℝ → ℝ) (hg : MemLp g 2 μ) (S : Set ℝ) :
    ‖∫ x in S, g x ∂μ‖ ^ 2 ≤ μ.real univ * ∫ x, g x ^ 2 ∂μ := by
  have hi := hg.integrable (by norm_num : (1:ℝ≥0∞) ≤ 2)
  have hh := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
    (by simpa using hg : MemLp g (ENNReal.ofReal 2) μ)
    (memLp_const (μ := μ) (1:ℝ) : MemLp (fun _ : ℝ => (1:ℝ)) (ENNReal.ofReal 2) μ)
  have hcs : (∫ x, ‖g x‖ ∂μ) ≤
      Real.sqrt (∫ x, g x ^ 2 ∂μ) * Real.sqrt (μ.real univ) := by
    simpa only [Real.norm_eq_abs,abs_one,mul_one,Real.rpow_two,sq_abs,one_pow,
      integral_const,smul_eq_mul,← Real.sqrt_eq_rpow] using hh
  have hn : ‖∫ x in S, g x ∂μ‖ ≤
      Real.sqrt (∫ x, g x ^ 2 ∂μ) * Real.sqrt (μ.real univ) :=
    (norm_integral_le_integral_norm _).trans
      ((setIntegral_le_integral hi.norm (.of_forall fun x => norm_nonneg _)).trans hcs)
  have h := pow_le_pow_left₀ (norm_nonneg _) hn 2
  rw [mul_pow,Real.sq_sqrt (integral_nonneg fun x => sq_nonneg _),
    Real.sq_sqrt (show 0 ≤ μ.real univ from ENNReal.toReal_nonneg),mul_comm] at h
  exact h

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.cumulative_integral_square_bound

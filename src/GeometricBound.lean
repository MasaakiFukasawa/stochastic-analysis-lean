import SeriesBound
open MeasureTheory Filter Set
open scoped ENNReal Topology
namespace Asakura

/-- Sum an explicit geometric bound on Lp norms. -/
theorem geometric_lp_norm_sum {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (p : ℝ≥0∞) (f : ℕ → Ω → ℝ)
    (C r : ℝ) (hC : 0 ≤ C) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (h : ∀ n, eLpNorm (f n) p μ ≤ ENNReal.ofReal (C * r^n)) :
    (∑' n, eLpNorm (f n) p μ ≤ ENNReal.ofReal (C / (1-r))) ∧
    (∑' n, eLpNorm (f n) p μ ≠ ∞) := by
  have hr : |r| < 1 := by rwa [abs_of_nonneg hr0]
  have hsum : Summable (fun n : ℕ => C * r^n) :=
    (summable_geometric_of_abs_lt_one hr).mul_left C
  have heq : (∑' n : ℕ, ENNReal.ofReal (C * r^n)) = ENNReal.ofReal (C / (1-r)) := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => mul_nonneg hC (pow_nonneg hr0 n)) hsum,
      tsum_mul_left, tsum_geometric_of_abs_lt_one hr, div_eq_mul_inv]
  have hle : ∑' n, eLpNorm (f n) p μ ≤ ENNReal.ofReal (C / (1-r)) := by
    rw [← heq]
    exact ENNReal.tsum_le_tsum h
  exact ⟨hle, ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle⟩

/-- C.2: weighting geometrically decaying increments by q^n changes the ratio to q*r. -/
theorem weighted_geometric_lp {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (p : ℝ≥0∞) (K : ℕ → Ω → ℝ)
    (C q r : ℝ) (hC : 0 ≤ C) (hq : 0 ≤ q) (hr : 0 ≤ r) (hqr : q*r < 1)
    (h : ∀ n, eLpNorm (K n) p μ ≤ ENNReal.ofReal (C * r^n)) :
    ∑' n, eLpNorm (fun ω => q^n * K n ω) p μ ≤ ENNReal.ofReal (C / (1-q*r)) := by
  apply (geometric_lp_norm_sum μ p (fun n ω => q^n * K n ω)
    C (q*r) hC (mul_nonneg hq hr) hqr ?_).1
  intro n
  have heq : (fun ω => q^n * K n ω) = (q^n) • K n := by rfl
  rw [heq, eLpNorm_const_smul]
  calc
    ‖q^n‖ₑ * eLpNorm (K n) p μ ≤ ‖q^n‖ₑ * ENNReal.ofReal (C * r^n) :=
      mul_le_mul_of_nonneg_left (h n) (by positivity)
    _ = ENNReal.ofReal (C * (q*r)^n) := by
      rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (pow_nonneg hq n),
        ← ENNReal.ofReal_mul (pow_nonneg hq n), mul_pow]
      congr 1
      ring
end Asakura

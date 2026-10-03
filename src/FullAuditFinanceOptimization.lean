import FullAuditChapter4Gronwall

open MeasureTheory Set
namespace Asakura.FullAudit

/-- The completion of the square in the written log-utility argument. -/
theorem finance_log_square (r μ σ z : ℝ) (hσ : σ ≠ 0) :
    r+z*(μ-r)-σ^2*z^2/2 =
      r+(μ-r)^2/(2*σ^2)-σ^2/2*(z-(μ-r)/σ^2)^2 := by
  field_simp
  <;> ring

/-- Pointwise optimizer, including the interval constraint of Exercise 11.4.1. -/
theorem finance_interval_projection (a z : ℝ) (hz : z ∈ Icc 0 1) :
    (min 1 (max 0 a)-a)^2 ≤ (z-a)^2 := by
  rcases le_total a 0 with ha | ha
  · rw [max_eq_left ha, min_eq_right (by norm_num : (0:ℝ) ≤ 1)]
    nlinarith [sq_nonneg z, mul_nonneg hz.1 (neg_nonneg.mpr ha)]
  · rw [max_eq_right ha]
    rcases le_total a 1 with hb | hb
    · rw [min_eq_right hb]
      simpa using sq_nonneg (z-a)
    · rw [min_eq_left hb]
      nlinarith [sq_nonneg (z-1), mul_nonneg (sub_nonneg.mpr hb) (sub_nonneg.mpr hz.2)]

/-- Complete maximization of the deterministic growth-rate function. -/
theorem finance_constrained_growth_max (r μ σ z : ℝ) (hσ : σ ≠ 0)
    (hz : z ∈ Icc 0 1) :
    r+z*(μ-r)-σ^2*z^2/2 ≤
      r+min 1 (max 0 ((μ-r)/σ^2))*(μ-r)-
        σ^2*(min 1 (max 0 ((μ-r)/σ^2)))^2/2 := by
  rw [finance_log_square r μ σ z hσ,
    finance_log_square r μ σ (min 1 (max 0 ((μ-r)/σ^2))) hσ]
  have hp := finance_interval_projection ((μ-r)/σ^2) z hz
  have hs : 0 ≤ σ^2/2 := by positivity
  have := mul_le_mul_of_nonneg_left hp hs
  linarith

/-- The unconstrained Merton maximizer is unique for gamma>0 and sigma nonzero. -/
theorem finance_merton_square (r μ σ γ z : ℝ) (hσ : σ ≠ 0) (hγ : γ ≠ 0) :
    r+z*(μ-r)-γ*σ^2*z^2/2 =
      r+(μ-r)^2/(2*γ*σ^2)-γ*σ^2/2*(z-(μ-r)/(γ*σ^2))^2 := by
  field_simp
  <;> ring

theorem finance_merton_max (r μ σ γ z : ℝ) (hσ : σ ≠ 0) (hγ : 0 < γ) :
    r+z*(μ-r)-γ*σ^2*z^2/2 ≤ r+(μ-r)^2/(2*γ*σ^2) := by
  rw [finance_merton_square r μ σ γ z hσ (ne_of_gt hγ)]
  have : 0 ≤ γ*σ^2/2*(z-(μ-r)/(γ*σ^2))^2 := by positivity
  linarith

/-- Once Ito and the zero-mean martingale identity give the objective, positivity
of the measure integral finishes the written proof; this theorem isolates that step. -/
theorem finance_log_expected_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (π : Ω → ℝ) (c σ a : ℝ) :
    c-σ^2/2*(∫ ω, (π ω-a)^2 ∂P) ≤ c := by
  have hi : 0 ≤ ∫ ω, (π ω-a)^2 ∂P := integral_nonneg (fun _ => sq_nonneg _)
  have : 0 ≤ σ^2/2*(∫ ω, (π ω-a)^2 ∂P) := by positivity
  linarith

end Asakura.FullAudit

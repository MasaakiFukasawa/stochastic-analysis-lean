import Mathlib.NumberTheory.ZetaValues

open Set
namespace Asakura

lemma bernoulli_two_eval (x : ℝ) :
    (Polynomial.map (algebraMap ℚ ℝ) (Polynomial.bernoulli 2)).eval x =
      x ^ 2 - x + 1 / 6 := by
  norm_num [Polynomial.bernoulli, Finset.sum_range_succ,
    bernoulli_eq_bernoulli'_of_ne_one, bernoulli'_two, _root_.bernoulli_one]
  <;> ring

lemma cosine_series (x : ℝ) (hx : x ∈ Icc 0 1) :
    HasSum (fun n : ℕ => 1 / (n : ℝ) ^ 2 * Real.cos (2 * Real.pi * n * x))
      (Real.pi ^ 2 * (x ^ 2 - x + 1 / 6)) := by
  have h := hasSum_one_div_nat_pow_mul_cos (k := 1) (by decide) hx
  norm_num only [Nat.mul_one, Nat.add_one, Nat.factorial_succ, Nat.factorial_zero,
    Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat, mul_one, neg_one_sq] at h
  rw [bernoulli_two_eval] at h
  convert h using 1 <;> ring

/-- The covariance identity used in the manuscript, proved by absolutely
convergent cosine series. The n=0 summand is zero. -/
theorem brownian_fourier_covariance (s t : ℝ) (hs : s ∈ Icc 0 1)
    (ht : t ∈ Icc 0 1) :
    HasSum (fun n : ℕ =>
      2 * Real.sin (Real.pi * n * s) * Real.sin (Real.pi * n * t) /
        (Real.pi ^ 2 * (n : ℝ) ^ 2)) (min s t - s * t) := by
  wlog hst : s ≤ t generalizing s t
  · have h := this t s ht hs (le_of_not_ge hst)
    convert h using 1
    · ext n; ring
    · rw [min_comm]; ring
  have h₁ := cosine_series ((t - s) / 2) (by constructor <;> linarith [hs.1, ht.2])
  have h₂ := cosine_series ((t + s) / 2) (by constructor <;> linarith [hs.1, hs.2, ht.1, ht.2])
  have h := (h₁.sub h₂).div_const (Real.pi ^ 2)
  convert h using 1
  · ext n
    rw [Real.two_mul_sin_mul_sin]
    have e₁ : 2 * Real.pi * (n : ℝ) * ((t - s) / 2) =
        -(Real.pi * n * s - Real.pi * n * t) := by ring
    have e₂ : 2 * Real.pi * (n : ℝ) * ((t + s) / 2) =
        Real.pi * n * s + Real.pi * n * t := by ring
    rw [e₁, e₂, Real.cos_neg]
    ring
  · rw [min_eq_left hst]
    field_simp [Real.pi_ne_zero]
    <;> ring

end Asakura

import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

open MeasureTheory Set
namespace Asakura

/-- The past kernel in the Mandelbrot–Van Ness formula. -/
noncomputable def mvnPastKernel (a t s : ℝ) : ℝ := (t+s)^a-s^a

lemma mvn_past_tail_bound (a t s : ℝ) (ha : a ≤ 1) (ht : 0 ≤ t) (hs : 0 < s) :
    |mvnPastKernel a t s| ≤ (|a| * t) * s^(a-1) := by
  have hd : ∀ x ∈ Icc s (t+s), HasDerivWithinAt (fun x : ℝ => x^a)
      (a*x^(a-1)) (Icc s (t+s)) x := by
    intro x hx
    exact (Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt (hs.trans_le hx.1)))).hasDerivWithinAt
  have hb : ∀ x ∈ Ico s (t+s), ‖a*x^(a-1)‖ ≤ |a| *s^(a-1) := by
    intro x hx
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (hs.trans_le hx.1).le _)]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hs hx.1 (by linarith)) (abs_nonneg _)
  have hh := norm_image_sub_le_of_norm_deriv_le_segment' hd hb (t+s) ⟨by linarith,le_rfl⟩
  simpa [mvnPastKernel, Real.norm_eq_abs, mul_assoc, mul_left_comm, mul_comm] using hh

lemma mvn_past_square_bound (a t s : ℝ) (ht : 0 ≤ t) (hs : 0 ≤ s) :
    (mvnPastKernel a t s)^2 ≤ 2*((t+s)^(2*a)+s^(2*a)) := by
  have h₁ : ((t+s)^a)^2 = (t+s)^(2*a) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith : 0 ≤ t+s)]
    congr 1; ring
  have h₂ : (s^a)^2 = s^(2*a) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hs]
    congr 1; ring
  unfold mvnPastKernel
  nlinarith [sq_nonneg ((t+s)^a+s^a)]

lemma mvn_past_tail_square_bound (a t s : ℝ) (ha : a ≤ 1) (ht : 0 ≤ t) (hs : 0 < s) :
    (mvnPastKernel a t s)^2 ≤ (|a| *t)^2 * s^(2*a-2) := by
  have h := mvn_past_tail_bound a t s ha ht hs
  have hb : 0 ≤ (|a| *t)*s^(a-1) := by positivity
  have hh := pow_le_pow_left₀ (abs_nonneg _) h 2
  have he : (s^(a-1))^2 = s^(2*a-2) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hs.le]
    congr 1; ring
  rw [sq_abs,mul_pow,he] at hh
  exact hh
end Asakura

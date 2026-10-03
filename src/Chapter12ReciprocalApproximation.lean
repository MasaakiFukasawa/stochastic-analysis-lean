import Chapter12ExponentialApproximation
import Mathlib.Analysis.Calculus.Deriv.Pow

open Filter
open scoped Topology
namespace Asakura.Chapter12
set_option maxHeartbeats 1400000

noncomputable def regularizedReciprocal (ε x : ℝ) := x/(x^2+ε)
noncomputable def regularizedReciprocalDeriv (ε x : ℝ) := (ε-x^2)/(x^2+ε)^2

theorem regularized_reciprocal_hasDerivAt (ε : ℝ) (hε : 0 < ε) (x : ℝ) :
    HasDerivAt (regularizedReciprocal ε) (regularizedReciprocalDeriv ε x) x := by
  have hden : x^2+ε ≠ 0 := ne_of_gt (by positivity)
  convert (hasDerivAt_id x).div (((hasDerivAt_id x).pow 2).add_const ε) hden using 1
  · rfl
  · dsimp [regularizedReciprocalDeriv]
    congr 1
    ring

theorem regularized_reciprocal_derivative_continuous (ε : ℝ) (hε : 0 < ε) :
    Continuous (regularizedReciprocalDeriv ε) := by
  unfold regularizedReciprocalDeriv
  exact (continuous_const.sub (continuous_id.pow 2)).div
    (((continuous_id.pow 2).add continuous_const).pow 2)
    (fun x => pow_ne_zero 2 (ne_of_gt (by positivity)))

theorem regularized_reciprocal_derivative_bound (ε : ℝ) (hε : 0 < ε) (x : ℝ) :
    |regularizedReciprocalDeriv ε x| ≤ 1/ε := by
  have hd : 0 < x^2+ε := by positivity
  have hn : |ε-x^2| ≤ x^2+ε := abs_le.mpr ⟨by nlinarith [sq_nonneg x],by nlinarith [sq_nonneg x]⟩
  calc
    _ = |ε-x^2|/(x^2+ε)^2 := by simp [regularizedReciprocalDeriv,abs_div,abs_of_pos (sq_pos_of_pos hd)]
    _ ≤ (x^2+ε)/(x^2+ε)^2 := div_le_div_of_nonneg_right hn (sq_nonneg _)
    _ = 1/(x^2+ε) := by field_simp
    _ ≤ 1/ε := one_div_le_one_div_of_le hε (by nlinarith [sq_nonneg x])

theorem regularized_reciprocal_positive_bounds (ε : ℝ) (hε : 0 < ε) (x : ℝ) (hx : 0 < x) :
    |regularizedReciprocal ε x| ≤ |x⁻¹| ∧
    |regularizedReciprocalDeriv ε x| ≤ |-(x⁻¹)^2| := by
  have hd : 0 < x^2+ε := by positivity
  have hn : |ε-x^2| ≤ x^2+ε := abs_le.mpr ⟨by nlinarith [sq_nonneg x],by nlinarith [sq_nonneg x]⟩
  constructor
  · simp only [regularizedReciprocal,abs_div,abs_of_pos hx,abs_of_pos hd,abs_of_pos (inv_pos.mpr hx)]
    apply (div_le_iff₀ hd).mpr
    have he : x⁻¹*x^2 = x := by field_simp
    rw [mul_add,he]
    exact le_add_of_nonneg_right (by positivity)
  · calc
      _ = |ε-x^2|/(x^2+ε)^2 := by simp [regularizedReciprocalDeriv,abs_div,abs_of_pos (sq_pos_of_pos hd)]
      _ ≤ (x^2+ε)/(x^2+ε)^2 := div_le_div_of_nonneg_right hn (sq_nonneg _)
      _ = 1/(x^2+ε) := by field_simp
      _ ≤ 1/x^2 := one_div_le_one_div_of_le (sq_pos_of_pos hx) (by linarith)
      _ = |-(x⁻¹)^2| := by simp [one_div,inv_pow]

theorem regularized_reciprocal_limits (x : ℝ) (hx : 0 < x) :
    Tendsto (fun n : ℕ => regularizedReciprocal (1/(n+1)) x) atTop (𝓝 x⁻¹) ∧
    Tendsto (fun n : ℕ => regularizedReciprocalDeriv (1/(n+1)) x) atTop (𝓝 (-(x⁻¹)^2)) := by
  have he : Tendsto (fun n : ℕ => (1:ℝ)/(n+1)) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hn : x^2 ≠ 0 := pow_ne_zero 2 hx.ne'
  have hv : x/x^2 = x⁻¹ := by field_simp
  have hd : (-x^2)/(x^2)^2 = -(x⁻¹)^2 := by field_simp
  constructor
  · have ht := (tendsto_const_nhds (x := x)).div ((tendsto_const_nhds (x := x^2)).add he) (by simpa using hn)
    simp only [add_zero,hv] at ht
    exact ht
  · have ht := (he.sub (tendsto_const_nhds (x := x^2))).div (((tendsto_const_nhds (x := x^2)).add he).pow 2)
        (by simpa using pow_ne_zero 2 hn)
    simp only [add_zero,zero_sub,hd] at ht
    exact ht

end Asakura.Chapter12

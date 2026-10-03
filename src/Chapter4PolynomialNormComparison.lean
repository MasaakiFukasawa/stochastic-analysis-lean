import Chapter4VectorPowerGrowth

open MeasureTheory Set
open scoped BigOperators
namespace Asakura.Chapter4

/-- Euclidean polynomial growth implies the sup-norm growth used in the
finite-coordinate SDE construction, with only a change of constant. -/
theorem euclidean_polynomial_growth_to_pi {dim : ℕ} (x : Fin dim → ℝ)
    (N : ℕ) (C z : ℝ) (hC : 0≤C)
    (hz : |z|≤C*(1+(Real.sqrt (∑ i,x i^2))^N)) :
    |z|≤(C*(1+((dim:ℝ)+1)^N))*(1+‖x‖^N) := by
  have hs : (∑ i,x i^2)≤(dim:ℝ)*‖x‖^2 := by
    calc
      _ ≤ ∑ _i : Fin dim,‖x‖^2 := Finset.sum_le_sum (fun i _ => by
        simpa only [Real.norm_eq_abs,sq_abs] using
          pow_le_pow_left₀ (norm_nonneg (x i)) (norm_le_pi_norm x i) 2)
      _ = _ := by simp
  have he : Real.sqrt (∑ i,x i^2)≤((dim:ℝ)+1)*‖x‖ := by
    apply (Real.sqrt_le_iff).2
    constructor
    · positivity
    · nlinarith [sq_nonneg ‖x‖,Nat.cast_nonneg (α:=ℝ) dim,
        mul_nonneg (show 0≤(dim:ℝ)*((dim:ℝ)+1) by positivity) (sq_nonneg ‖x‖)]
  have hp := pow_le_pow_left₀ (Real.sqrt_nonneg _) he N
  rw [mul_pow] at hp
  have hc := mul_le_mul_of_nonneg_left (add_le_add (le_refl (1:ℝ)) hp) hC
  have hn : 0≤‖x‖^N := by positivity
  have hd : 0≤((dim:ℝ)+1)^N := by positivity
  nlinarith [mul_nonneg hC hn,mul_nonneg hC hd]

end Asakura.Chapter4

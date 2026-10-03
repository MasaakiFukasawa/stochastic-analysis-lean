import Chapter8GeneratorGrowthBridge

open scoped NNReal BigOperators
namespace Asakura.Chapter8
set_option maxHeartbeats 1000000

theorem lipschitz_linear_growth {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    (b : E → F) (L : ℝ≥0) (hb : LipschitzWith L b) :
    ∃ C : ℝ,0≤C ∧ ∀ x,‖b x‖≤C*(1+‖x‖) := by
  refine ⟨(L:ℝ)+‖b 0‖,by positivity,?_⟩
  intro x
  have h := hb.dist_le_mul x 0
  simp only [dist_eq_norm,sub_zero] at h
  have hn : ‖b x‖≤‖b x-b 0‖+‖b 0‖ := by
    simpa only [sub_add_cancel] using norm_add_le (b x-b 0) (b 0)
  nlinarith [norm_nonneg (b 0),norm_nonneg x,L.coe_nonneg]

theorem lipschitz_square_coordinates {d : ℕ}
    (b : (Fin d → ℝ) → (Fin d → ℝ)) (L : ℝ≥0) (hb : LipschitzWith L b) :
    ∀ x y,(∑ i,(b x i-b y i)^2)≤((d:ℝ)*(L:ℝ)^2)*∑ i,(x i-y i)^2 := by
  intro x y
  have h := hb.dist_le_mul x y
  simp only [dist_eq_norm] at h
  have hp i : (b x i-b y i)^2≤(L:ℝ)^2*‖x-y‖^2 := by
    have hn := (norm_le_pi_norm (b x-b y) i).trans h
    have hs := pow_le_pow_left₀ (norm_nonneg ((b x-b y) i)) hn 2
    simpa only [Pi.sub_apply,Real.norm_eq_abs,sq_abs,mul_pow] using hs
  calc
    _ ≤ ∑ _i : Fin d,(L:ℝ)^2*‖x-y‖^2 := Finset.sum_le_sum (fun i _ => hp i)
    _ = (d:ℝ)*(L:ℝ)^2*‖x-y‖^2 := by simp; ring
    _ ≤ ((d:ℝ)*(L:ℝ)^2)*∑ i,(x i-y i)^2 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [Pi.sub_apply] using Asakura.Chapter3Complete.pi_norm_sq_le_sum_sq (x-y)

end Asakura.Chapter8

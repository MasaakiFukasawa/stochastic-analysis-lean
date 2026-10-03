import Mathlib.Analysis.InnerProductSpace.PiL2

open scoped ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false

/-- A linear isometry acts coordinatewise on a finite Hilbert direct sum. -/
noncomputable def finitePiIsometry {ι H E : Type*} [Fintype ι]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (J : H →ₗᵢ[ℝ] E) : PiLp 2 (fun _ : ι => H) →ₗᵢ[ℝ] PiLp 2 (fun _ : ι => E) where
  toFun x := WithLp.toLp 2 (fun i => J (x i))
  map_add' := by intro x y; ext i; simp [PiLp.add_apply]
  map_smul' := by intro a x; ext i; simp [PiLp.smul_apply]
  norm_map' := by
    intro x
    have h : ‖WithLp.toLp 2 (fun i => J (x i))‖^2 = ‖x‖^2 := by
      rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
      apply Finset.sum_congr rfl
      intro i _
      exact congrArg (fun r : ℝ => r^2) (J.norm_map (x i))
    change ‖WithLp.toLp 2 (fun i => J (x i))‖ = ‖x‖
    nlinarith [norm_nonneg (WithLp.toLp 2 (fun i => J (x i))), norm_nonneg x]

end Asakura.Chapter12

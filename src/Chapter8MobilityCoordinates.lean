import Chapter8DiagonalCoordinates
import Chapter8SymmetricNormBound

open scoped BigOperators RealInnerProductSpace
namespace Asakura.Chapter8
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

/-- Diagonalizing a positive symmetric mobility constructs the actual
inverse-mobility norm and its sharp lower-eigenvalue comparison. -/
theorem mobility_coordinates {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (M : E ≃L[ℝ] E) (hs : M.toContinuousLinearMap.toLinearMap.IsSymmetric)
    (α : ℝ) (hα : 0<α) (hM : ∀ z,α*‖z‖^2≤⟪z,M z⟫) :
    ∃ A : E ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)),
      (∀ x y,⟪A x,A (M y)⟫=⟪x,y⟫) ∧
      (∀ x,‖A x‖^2=⟪x,M.symm x⟫) ∧ (∀ x,α*‖A x‖^2≤‖x‖^2) := by
  let B := hs.eigenvectorBasis rfl
  let ev := hs.eigenvalues rfl
  have hev i : M (B i)=ev i • B i := hs.apply_eigenvectorBasis rfl i
  have hevl i : α≤ev i := by
    have hh := hM (B i)
    rw [hev,inner_smul_right,real_inner_self_eq_norm_sq,B.orthonormal.norm_eq_one] at hh
    simpa using hh
  have hp i : 0<ev i := hα.trans_le (hevl i)
  let c := fun i => (Real.sqrt (ev i))⁻¹
  have hc i : c i≠0 := inv_ne_zero (Real.sqrt_pos.mpr (hp i)).ne'
  let A := B.repr.toContinuousLinearEquiv.trans (diagonalEuclideanEquiv c hc)
  have hA x i : A x i=c i*⟪B i,x⟫ := by
    change c i*(B.repr x i)=_
    rw [B.repr_apply_apply]
  have hcoord y i : ⟪B i,M y⟫=ev i*⟪B i,y⟫ := by
    have hh : ⟪M (B i),y⟫=⟪B i,M y⟫ := hs (B i) y
    rw [←hh,hev,real_inner_smul_left]
  have hcoef i : (c i)^2*ev i=1 := by
    dsimp [c]
    rw [inv_pow,Real.sq_sqrt (hp i).le,inv_mul_cancel₀ (hp i).ne']
  have hinner x y : ⟪A x,A (M y)⟫=⟪x,y⟫ := by
    rw [PiLp.inner_apply]
    have hcross : (∑ i,⟪B i,x⟫*⟪B i,y⟫)=⟪x,y⟫ := by
      simpa only [real_inner_comm x] using B.sum_inner_mul_inner x y
    rw [←hcross]
    apply Finset.sum_congr rfl
    intro i _
    simp only [RCLike.inner_apply,starRingEnd_apply,star_trivial,hA,hcoord]
    calc
      _ = ((c i)^2*ev i)*(⟪B i,x⟫*⟪B i,y⟫) := by ring
      _ = _ := by rw [hcoef,one_mul]
  refine ⟨A,hinner,?_,?_⟩
  · intro x
    have hh := hinner x (M.symm x)
    simpa only [M.apply_symm_apply,real_inner_self_eq_norm_sq] using hh
  · intro x
    rw [EuclideanSpace.real_norm_sq_eq,←B.sum_sq_inner_right x,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [hA,mul_pow]
    have hh : α*(c i)^2≤1 := by
      dsimp [c]
      rw [inv_pow,Real.sq_sqrt (hp i).le,←div_eq_mul_inv]
      exact (div_le_one (hp i)).mpr (hevl i)
    nlinarith [mul_le_mul_of_nonneg_right hh (sq_nonneg ⟪B i,x⟫)]

end Asakura.Chapter8

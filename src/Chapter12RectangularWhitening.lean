import Mathlib.Analysis.Matrix.Order

open Matrix
open scoped MatrixOrder
namespace Asakura.Chapter12
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

theorem rectangular_whitening {n d:Type*} [Fintype n] [Fintype d] [DecidableEq n] [DecidableEq d]
    (S:Matrix n d ℝ) (hS:(S*S.transpose).PosDef) :
    ∃L:Matrix n n ℝ,∃A:Matrix n d ℝ,IsUnit L ∧ L.transpose=L ∧ L*L=S*S.transpose ∧
      A*A.transpose=1 ∧ L*A=S := by
  let G := S*S.transpose
  let L := CFC.sqrt G
  have hL:L.transpose=L := by
    have h := (CFC.sqrt_nonneg G).posSemidef.isHermitian
    simpa only [Matrix.IsHermitian,Matrix.conjTranspose_eq_transpose_of_trivial] using h
  have hLL:L*L=G := by simpa only [pow_two] using CFC.sq_sqrt G hS.posSemidef.nonneg
  have hdet:0<L.det := by
    rw [show L.det=Real.sqrt G.det from by simpa only [RCLike.sqrt_real] using hS.posSemidef.det_sqrt]
    exact Real.sqrt_pos.mpr hS.det_pos
  have hLu:IsUnit L := (Matrix.isUnit_iff_isUnit_det L).mpr (isUnit_iff_ne_zero.mpr (ne_of_gt hdet))
  change L*L=S*S.transpose at hLL
  let A := L⁻¹*S
  have hLinv:IsUnit L.det := (Matrix.isUnit_iff_isUnit_det L).mp hLu
  refine ⟨L,A,hLu,hL,hLL,?_,?_⟩
  · change (L⁻¹*S)*(L⁻¹*S).transpose=1
    rw [Matrix.transpose_mul,←Matrix.mul_assoc,Matrix.mul_assoc L⁻¹ S S.transpose,←hLL,
      ←Matrix.mul_assoc L⁻¹ L L,Matrix.nonsing_inv_mul L hLinv,Matrix.one_mul,
      Matrix.transpose_nonsing_inv,hL,Matrix.mul_nonsing_inv L hLinv]
  · change L*(L⁻¹*S)=S
    rw [←Matrix.mul_assoc,Matrix.mul_nonsing_inv L hLinv,Matrix.one_mul]
end Asakura.Chapter12
#print axioms Asakura.Chapter12.rectangular_whitening

import Chapter12MatrixNoiseReduction
import Chapter12BrownianForcingCovariance

open Matrix
open scoped BigOperators RealInnerProductSpace
namespace Asakura.Chapter12
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

theorem column_ellipticity_posDef {n d:ℕ} (v:Fin d → EuclideanSpace ℝ (Fin n))
    (c:ℝ) (hc:0<c) (hv:∀z:EuclideanSpace ℝ (Fin n),c*‖z‖^2≤∑j,(inner ℝ z (v j))^2) :
    let σ:Matrix (Fin n) (Fin d) ℝ := fun i j => v j i
    (σ*σ.transpose).PosDef := by
  dsimp only
  let σ:Matrix (Fin n) (Fin d) ℝ := fun i j => v j i
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using Matrix.isHermitian_mul_conjTranspose_self σ
  intro z hz
  have hnorm:0<‖WithLp.toLp 2 z‖^2 := sq_pos_of_pos (norm_pos_iff.mpr (by simpa using hz))
  have hpos := lt_of_lt_of_le (mul_pos hc hnorm) (hv (WithLp.toLp 2 z))
  convert hpos using 1
  change z ⬝ᵥ ((σ*σ.transpose).mulVec z)=∑j,(inner ℝ (WithLp.toLp 2 z) (v j))^2
  rw [←Matrix.mulVec_mulVec,Matrix.dotProduct_mulVec,Matrix.mulVec_transpose]
  simp only [dotProduct,Matrix.vecMul,EuclideanSpace.inner_eq_star_dotProduct,star_trivial,σ]
  apply Finset.sum_congr rfl
  intro j _
  rw [pow_two]
  congr 1 <;> apply Finset.sum_congr rfl <;> intros <;> exact mul_comm _ _
end Asakura.Chapter12
#print axioms Asakura.Chapter12.column_ellipticity_posDef

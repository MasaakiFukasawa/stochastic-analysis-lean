import Chapter10MatrixCovarianceUniqueness

open Set Matrix
open scoped NNReal Matrix.Norms.Elementwise
namespace Asakura.Chapter10
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

/-- Entrywise truncation used only to construct a global auxiliary ODE. -/
noncomputable def matrixClip {d : ℕ} (R : ℝ≥0) (S : Matrix (Fin d) (Fin d) ℝ) :
    Matrix (Fin d) (Fin d) ℝ := fun i j => (projIcc (-(R:ℝ)) R (by linarith [R.coe_nonneg]) (S i j)).val

theorem matrixClip_norm_le {d : ℕ} (R : ℝ≥0) (S : Matrix (Fin d) (Fin d) ℝ) :
    ‖matrixClip R S‖≤R := by
  apply (pi_norm_le_iff_of_nonneg R.coe_nonneg).mpr
  intro i
  apply (pi_norm_le_iff_of_nonneg R.coe_nonneg).mpr
  intro j
  rw [Real.norm_eq_abs,abs_le]
  exact (projIcc (-(R:ℝ)) R (by linarith [R.coe_nonneg]) (S i j)).property

theorem matrixClip_eq_self {d : ℕ} (R : ℝ≥0) (S : Matrix (Fin d) (Fin d) ℝ) (hS : ‖S‖≤R) :
    matrixClip R S=S := by
  ext i j
  have hn := ((norm_le_pi_norm (S i) j).trans (norm_le_pi_norm S i)).trans hS
  rw [Real.norm_eq_abs,abs_le] at hn
  simp only [matrixClip,projIcc]
  simp [min_eq_right hn.2,max_eq_right hn.1]

theorem matrixClip_lipschitz {d : ℕ} (R : ℝ≥0) :
    LipschitzWith 1 (matrixClip (d := d) R) := by
  apply LipschitzWith.of_dist_le_mul
  intro S U
  simp only [dist_eq_norm,NNReal.coe_one,one_mul]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro i
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro j
  have hh := (LipschitzWith.projIcc (show -(R:ℝ)≤R by linarith [R.coe_nonneg])).dist_le_mul (S i j) (U i j)
  simp only [NNReal.coe_one,one_mul,Subtype.dist_eq,dist_eq_norm] at hh
  exact hh.trans ((norm_le_pi_norm ((S-U) i) j).trans (norm_le_pi_norm (S-U) i))

theorem matrixClip_transpose {d : ℕ} (R : ℝ≥0) (S : Matrix (Fin d) (Fin d) ℝ) :
    matrixClip R S.transpose=(matrixClip R S).transpose := rfl

end Asakura.Chapter10

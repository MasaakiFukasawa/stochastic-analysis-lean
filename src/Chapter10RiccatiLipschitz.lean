import Chapter10MatrixClip

open Matrix
open scoped NNReal Matrix.Norms.Elementwise
namespace Asakura.Chapter10
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

lemma elementwise_matrix_triple_bound {d : ℕ} (U V W : Matrix (Fin d) (Fin d) ℝ) :
    ‖U*V*W‖≤(d:ℝ)^2*‖U‖*‖V‖*‖W‖ := by
  calc
    _ ≤ (d:ℝ)*‖U*V‖*‖W‖ := elementwise_matrix_product_bound _ _
    _ ≤ (d:ℝ)*((d:ℝ)*‖U‖*‖V‖)*‖W‖ := by gcongr; exact elementwise_matrix_product_bound _ _
    _ = _ := by ring

/-- Polynomial Riccati drift is Lipschitz on every bounded matrix set. -/
theorem riccati_bounded_lipschitz {d : ℕ} (A H Q U V : Matrix (Fin d) (Fin d) ℝ)
    (R : ℝ) (hR : 0≤R) (hU : ‖U‖≤R) (hV : ‖V‖≤R) :
    ‖(A*U+U*A.transpose+Q-U*H*U)-(A*V+V*A.transpose+Q-V*H*V)‖≤
      (2*(d:ℝ)*‖A‖+2*(d:ℝ)^2*‖H‖*R)*‖U-V‖ := by
  have he : (A*U+U*A.transpose+Q-U*H*U)-(A*V+V*A.transpose+Q-V*H*V)=
      (A*(U-V)+(U-V)*A.transpose)-((U-V)*H*U+V*H*(U-V)) := by noncomm_ring
  rw [he]
  have h1 := elementwise_matrix_product_bound A (U-V)
  have h2 := elementwise_matrix_product_bound (U-V) A.transpose
  rw [Matrix.norm_transpose] at h2
  have h3 : ‖(U-V)*H*U‖≤(d:ℝ)^2*‖U-V‖*‖H‖*R :=
    (elementwise_matrix_triple_bound _ _ _).trans (by gcongr)
  have h4 : ‖V*H*(U-V)‖≤(d:ℝ)^2*R*‖H‖*‖U-V‖ :=
    (elementwise_matrix_triple_bound _ _ _).trans (by gcongr)
  have h5 := norm_sub_le (A*(U-V)+(U-V)*A.transpose) ((U-V)*H*U+V*H*(U-V))
  have h6 := norm_add_le (A*(U-V)) ((U-V)*A.transpose)
  have h7 := norm_add_le ((U-V)*H*U) (V*H*(U-V))
  nlinarith

/-- A globally Lipschitz truncation agrees with the Riccati drift inside
the matrix ball. It provides an actual global auxiliary solution. -/
theorem clipped_riccati_lipschitz {d : ℕ} (A H Q : Matrix (Fin d) (Fin d) ℝ) (R : ℝ≥0) :
    LipschitzWith ⟨2*(d:ℝ)*‖A‖+2*(d:ℝ)^2*‖H‖*R,by positivity⟩
      (fun S => A*matrixClip R S+matrixClip R S*A.transpose+Q-matrixClip R S*H*matrixClip R S) := by
  apply LipschitzWith.of_dist_le_mul
  intro U V
  simp only [dist_eq_norm,NNReal.coe_mk]
  have hh := riccati_bounded_lipschitz A H Q (matrixClip R U) (matrixClip R V) R R.coe_nonneg
    (matrixClip_norm_le R U) (matrixClip_norm_le R V)
  have hc := (matrixClip_lipschitz (d := d) R).dist_le_mul U V
  simp only [dist_eq_norm,NNReal.coe_one,one_mul] at hc
  exact hh.trans (mul_le_mul_of_nonneg_left hc (by positivity))

end Asakura.Chapter10

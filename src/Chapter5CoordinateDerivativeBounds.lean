import Chapter5BoundedCylinderData

open scoped NNReal BigOperators
namespace Asakura.Chapter5
set_option maxHeartbeats 2400000

lemma finite_coordinate_operator_bound {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (k : ℕ) (L : (Fin k → ℝ) →L[ℝ] G) :
    ‖L‖≤∑ i,‖L (Pi.single i 1)‖ := by
  classical
  apply ContinuousLinearMap.opNorm_le_bound _ (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  intro x
  have he : x=∑ i : Fin k,x i • Pi.single i 1 := by ext i; simp [Pi.single_apply,eq_comm]
  calc
    ‖L x‖ = ‖∑ i : Fin k,x i • L (Pi.single i 1)‖ := by
      conv_lhs => rw [he,map_sum]
      simp only [map_smul]
    _ ≤ ∑ i : Fin k,‖x i • L (Pi.single i 1)‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin k,‖L (Pi.single i 1)‖*‖x‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul,mul_comm]
      exact mul_le_mul_of_nonneg_left (norm_le_pi_norm x i) (norm_nonneg _)
    _ = (∑ i,‖L (Pi.single i 1)‖)*‖x‖ := (Finset.sum_mul ..).symm

/-- Coordinate bounds in the printed assumption supply operator-norm
bounds for the Frechet derivative data used by the Gaussian recursion. -/
theorem bounded_coordinate_C2_data (k : ℕ) (f : (Fin k → ℝ) → ℝ) (hf : ContDiff ℝ 2 f)
    (C K : ℝ≥0)
    (hC : ∀ x i,|fderiv ℝ f x (Pi.single i 1)|≤C)
    (hK : ∀ x i j,|fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single j 1)|≤K) :
    ∃ u : SmoothCylinderData (Fin k → ℝ),u.value=f := by
  apply bounded_C2_cylinder_data f hf ((k:ℝ≥0)*C) ((k:ℝ≥0)^2*K)
  · intro x
    apply (finite_coordinate_operator_bound k (fderiv ℝ f x)).trans
    calc
      _ ≤ ∑ _ : Fin k,(C:ℝ) := Finset.sum_le_sum (fun i _ => hC x i)
      _ = _ := by simp
  · intro x
    apply (finite_coordinate_operator_bound k (fderiv ℝ (fderiv ℝ f) x)).trans
    calc
      _ ≤ ∑ i : Fin k,∑ j : Fin k,|fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single j 1)| :=
        Finset.sum_le_sum (fun i _ => finite_coordinate_operator_bound k _)
      _ ≤ ∑ _ : Fin k,∑ _ : Fin k,(K:ℝ) :=
        Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hK x i j))
      _ = _ := by simp; ring

end Asakura.Chapter5

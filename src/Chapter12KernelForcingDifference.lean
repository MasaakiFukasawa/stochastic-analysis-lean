import Chapter12KernelForcingOperator

open scoped BigOperators RealInnerProductSpace
namespace Asakura.Chapter12
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

theorem kernelForcingOperator_difference {n : ℕ} {J H E : Type*} [Fintype J]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : Fin n → H) (h g : J → H) (v : J → E) :
    kernelForcingOperator e h v-kernelForcingOperator e g v=
      kernelForcingOperator e (fun j => h j-g j) v := by
  unfold kernelForcingOperator
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [inner_sub_right]
  exact (sub_smul (inner ℝ (e i) (h j)) (inner ℝ (e i) (g j)) ((ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ).smulRight (v j))).symm

theorem kernelForcingOperator_difference_bound {n : ℕ} {J H E : Type*} [Fintype J]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : Fin n → H) (he : Orthonormal ℝ e) (h g : J → H) (v : J → E) :
    Real.sqrt (∑i,‖kernelForcingOperator e h v (Pi.single i 1)-kernelForcingOperator e g v (Pi.single i 1)‖^2)≤
      ∑j,‖v j‖*‖h j-g j‖ := by
  simp_rw [←ContinuousLinearMap.sub_apply,kernelForcingOperator_difference]
  exact kernelForcingOperator_array_bound e he _ v
end Asakura.Chapter12
#print axioms Asakura.Chapter12.kernelForcingOperator_difference_bound

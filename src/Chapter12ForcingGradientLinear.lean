import Chapter12ForcingGradientRiesz
import Chapter12CovarianceInverseDirections

open scoped RealInnerProductSpace
namespace Asakura.Chapter12
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] forcingGradient

theorem forcingGradient_linear_sum {H E K I:Type*} [Fintype I]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace K] [CompactSpace K]
    (S:C(K,E) → C(K,E)) (a:C(K,E)) (R:H →L[ℝ] C(K,E)) (ell:I → E →L[ℝ] ℝ)
    (c:I → ℝ) (t:K) :
    forcingGradient S a R (∑i,c i • ell i) t=∑i,c i • forcingGradient S a R (ell i) t := by
  apply ext_inner_right ℝ
  intro u
  simp only [forcingGradient_inner,sum_inner,real_inner_smul_left,ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply,smul_eq_mul]

theorem euclidean_inner_coordinate_functional {n:ℕ} (z:EuclideanSpace ℝ (Fin n)) :
    innerSL ℝ z=∑i,z i • (PiLp.proj 2 (fun _ : Fin n => ℝ) i) := by
  ext y
  simp only [ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,smul_eq_mul,innerSL_apply_apply,
    PiLp.inner_apply,PiLp.proj_apply,Real.inner_apply]

theorem derivativeGram_hermitian {H I:Type*} [Fintype I]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] (u:I → H) : (derivativeGram u).IsHermitian := by
  ext i j
  exact real_inner_comm _ _

theorem derivativeGram_quadratic {H I:Type*} [Fintype I]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] (u:I → H) (z:I → ℝ) :
    (∑i,z i*((derivativeGram u).mulVec z) i)=‖∑i,z i • u i‖^2 := by
  rw [←real_inner_self_eq_norm_sq]
  simp only [derivativeGram,Matrix.mulVec,dotProduct,Finset.mul_sum,sum_inner,inner_sum,
    real_inner_smul_left,real_inner_smul_right]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [real_inner_comm (u j) (u i)]
  ring
end Asakura.Chapter12
#print axioms Asakura.Chapter12.forcingGradient_linear_sum
#print axioms Asakura.Chapter12.euclidean_inner_coordinate_functional
#print axioms Asakura.Chapter12.derivativeGram_quadratic

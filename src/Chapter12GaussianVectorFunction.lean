import Chapter12GaussianDerivativeFlatten
import Chapter12GaussianTensorIndexOrder
import Chapter12GaussianPartialFrechet

open scoped ContDiff
namespace Asakura.Chapter12
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false

noncomputable def gaussianVectorFunction {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {N : ℕ} (u : Fin N → GaussianJet N) (e : Fin N → H) (x : Fin N → ℝ) : H :=
  ∑i,(u i).f x • e i

theorem gaussianVectorFunction_smooth {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {N : ℕ} (u : Fin N → GaussianJet N) (e : Fin N → H) :
    ContDiff ℝ ∞ (gaussianVectorFunction u e) :=
  ContDiff.sum (fun i _ => (u i).smooth.smul contDiff_const)

theorem gaussianVectorFunction_derivative {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {N : ℕ} (u : Fin N → GaussianJet N) (e : Fin N → H)
    (k : ℕ) (x : Fin N → ℝ) (a : Fin k → Fin N) :
    iteratedFDeriv ℝ k (gaussianVectorFunction u e) x (fun j => Pi.single (a j) 1)=
      ∑i,((u i).iteratedPartial (List.ofFn a)).f x • e i := by
  unfold gaussianVectorFunction
  rw [iteratedFDeriv_fun_sum_apply (f:=fun i z => (u i).f z • e i)
    (fun i _ => ((u i).smooth.smul contDiff_const).contDiffAt.of_le (by simp))]
  simp only [ContinuousMultilinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [iteratedFDeriv_smul_const_apply ((u i).smooth.contDiffAt.of_le (by simp))]
  rw [gaussian_partial_frechet]
  rfl

theorem gaussianVectorFunction_derivative_norm {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {n : ℕ} (u : Fin (n+1) → GaussianJet (n+1)) (e : Fin (n+1) → H) (he : Orthonormal ℝ e)
    (k : ℕ) (x : Fin (n+1) → ℝ) :
    Real.sqrt (∑a:Fin k → Fin (n+1),
      ‖iteratedFDeriv ℝ k (gaussianVectorFunction u e) x (fun j => Pi.single (a j) 1)‖^2)=
      gaussianDerivativeNorm u k x := by
  simp_rw [gaussianVectorFunction_derivative,orthonormal_sum_norm e he,
    Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
  rw [gaussian_derivative_norm_split,Finset.sum_comm]
end Asakura.Chapter12
#print axioms Asakura.Chapter12.gaussianVectorFunction_derivative_norm

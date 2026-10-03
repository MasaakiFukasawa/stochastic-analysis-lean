import Chapter12HilbertKernelForcing

open scoped BigOperators RealInnerProductSpace
namespace Asakura.Chapter12
set_option maxHeartbeats 2000000

noncomputable def hilbertCoordinates {H:Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {N:ℕ} (e:Fin N → H) : H →L[ℝ] (Fin N → ℝ) :=
  ContinuousLinearMap.pi (fun j => innerSL ℝ (e j))

@[simp] theorem hilbertCoordinates_apply {H:Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {N:ℕ} (e:Fin N → H) (u:H) (j:Fin N) : hilbertCoordinates e u j=inner ℝ (e j) u := rfl

theorem hilbert_kernel_factorization {K J H E:Type*}
    [TopologicalSpace K] [CompactSpace K] [Fintype J]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {N:ℕ} (e:Fin N → H) (h:J → C(K,H)) (v:J → E)
    (he:∀j t,h j t=∑a,inner ℝ (e a) (h j t) • e a) :
    hilbertKernelForcing h v=(kernelForcingPath e h v).comp (hilbertCoordinates e) := by
  ext u t
  simp only [hilbertKernelForcing_apply,ContinuousLinearMap.comp_apply,kernelForcingPath_apply,
    kernelForcingOperator,ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.proj_apply,hilbertCoordinates_apply]
  apply Finset.sum_congr rfl
  intro j hj
  have hh:inner ℝ (h j t) u=∑a,inner ℝ (e a) (h j t)*inner ℝ (e a) u := by
    conv_lhs => rw [he j t]
    simp [sum_inner,real_inner_smul_left]
  rw [hh,Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro a ha
  exact mul_smul _ _ _
end Asakura.Chapter12
#print axioms Asakura.Chapter12.hilbert_kernel_factorization

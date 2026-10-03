import Chapter12HilbertKernelArrayBound
import Chapter12ContinuousMapOperator

open scoped BigOperators Topology RealInnerProductSpace
namespace Asakura.Chapter12
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

noncomputable def kernelForcingOperator {n : ℕ} {J H E : Type*} [Fintype J]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : Fin n → H) (h : J → H) (v : J → E) : (Fin n → ℝ) →L[ℝ] E :=
  ∑j,∑i,inner ℝ (e i) (h j) • ((ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ).smulRight (v j))

theorem kernelForcingOperator_basis {n : ℕ} {J H E : Type*} [Fintype J]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : Fin n → H) (h : J → H) (v : J → E) (i : Fin n) :
    kernelForcingOperator e h v (Pi.single i 1)=∑j,inner ℝ (e i) (h j) • v j := by
  classical
  simp [kernelForcingOperator,Pi.single_apply,smul_smul]

theorem kernelForcingOperator_continuous {n : ℕ} {K J H E : Type*} [TopologicalSpace K] [Fintype J]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : Fin n → H) (h : K → J → H) (v : J → E) (hh : ∀j,Continuous (fun t => h t j)) :
    Continuous (fun t => kernelForcingOperator e (h t) v) := by
  unfold kernelForcingOperator
  apply continuous_finset_sum
  intro j _
  apply continuous_finset_sum
  intro i _
  have hc : Continuous (fun t : K => inner ℝ (e i) (h t j)) := continuous_const.inner (hh j)
  exact hc.smul (show Continuous (fun _ : K => ((ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ).smulRight (v j))) from continuous_const)

theorem kernelForcingOperator_array_bound {n : ℕ} {J H E : Type*} [Fintype J]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : Fin n → H) (he : Orthonormal ℝ e) (h : J → H) (v : J → E) :
    Real.sqrt (∑i,‖kernelForcingOperator e h v (Pi.single i 1)‖^2)≤∑j,‖v j‖*‖h j‖ := by
  simp_rw [kernelForcingOperator_basis]
  exact hilbert_kernel_array_bound e he h v
end Asakura.Chapter12
#print axioms Asakura.Chapter12.kernelForcingOperator_array_bound

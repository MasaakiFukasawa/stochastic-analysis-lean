import Chapter12KernelForcingPath

open scoped BigOperators
namespace Asakura.Chapter12
set_option maxHeartbeats 1600000

theorem kernel_forcing_representation {n : ℕ} {K J H E : Type*}
    [TopologicalSpace K] [CompactSpace K] [Fintype J]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : Fin n → H) (h : J → C(K,H)) (v : J → E) (z : Fin n → ℝ)
    (w : J → C(K,ℝ))
    (hw : ∀j t,w j t=∑i,inner ℝ (e i) (h j t)*z i) :
    kernelForcingPath e h v z=∑j,(⟨fun t => w j t • v j,(w j).continuous.smul continuous_const⟩ : C(K,E)) := by
  classical
  ext t
  simp only [kernelForcingPath_apply,kernelForcingOperator,
    ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.proj_apply,
    ContinuousMap.sum_apply,ContinuousMap.coe_mk]
  apply Finset.sum_congr rfl
  intro j _
  rw [hw j t,Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro i _
  exact (mul_smul _ _ _).symm
end Asakura.Chapter12
#print axioms Asakura.Chapter12.kernel_forcing_representation

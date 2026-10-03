import Chapter12KernelForcingOperator

open scoped Topology
namespace Asakura.Chapter12
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

noncomputable def kernelForcingPath {n : ℕ} {K J H E : Type*}
    [TopologicalSpace K] [CompactSpace K] [Fintype J]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : Fin n → H) (h : J → C(K,H)) (v : J → E) : (Fin n → ℝ) →L[ℝ] C(K,E) :=
  let R : C(K,(Fin n → ℝ) →L[ℝ] E) :=
    ⟨fun t => kernelForcingOperator e (fun j => h j t) v,
      kernelForcingOperator_continuous e (fun t j => h j t) v (fun j => (h j).continuous)⟩
  (continuousMapApply R).comp (ContinuousLinearMap.const ℝ K)

@[simp] theorem kernelForcingPath_apply {n : ℕ} {K J H E : Type*}
    [TopologicalSpace K] [CompactSpace K] [Fintype J]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : Fin n → H) (h : J → C(K,H)) (v : J → E) (z : Fin n → ℝ) (t : K) :
    kernelForcingPath e h v z t=kernelForcingOperator e (fun j => h j t) v z := rfl
end Asakura.Chapter12
#print axioms Asakura.Chapter12.kernelForcingPath_apply

import Chapter12VolterraVariations

open Set
open scoped Topology ContDiff NNReal
namespace Asakura.Chapter12
universe u
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

theorem path_derivative_evaluation {K E G : Type*}
    [TopologicalSpace K] [CompactSpace K]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (X : G → C(K,E)) (hX : ContDiff ℝ ∞ X) (k : ℕ) (z : G) (v : Fin k → G) (t : K) :
    iteratedFDeriv ℝ k (fun y => X y t) z v=(iteratedFDeriv ℝ k X z v) t := by
  let ev : C(K,E) →L[ℝ] E := ContinuousMap.evalCLM ℝ t
  exact congrArg (fun D => D v) (ev.iteratedFDeriv_comp_left hX.contDiffAt (by simp))

theorem path_remainder_continuous {K : Type*} {E G : Type u}
    [TopologicalSpace K] [CompactSpace K]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (b : E → E) (hb : ContDiff ℝ ∞ b)
    (hbound : ∀k:ℕ,1≤k → ∃C:ℝ≥0,∀x,‖iteratedFDeriv ℝ k b x‖≤(C:ℝ))
    (X : G → C(K,E)) (hX : ContDiff ℝ ∞ X)
    (n : ℕ) (z : G) (v : Fin (n+1) → G) :
    Continuous (fun t : K => higherChainRemainder (fun y => X y t) b (n+1) z v) := by
  let S := continuousMapSuperposition (K:=K) b hb.continuous
  have hS : ContDiff ℝ ∞ S := continuousMap_superposition_smooth b hb hbound
  have he t : higherChainRemainder (fun y => X y t) b (n+1) z v=
      (iteratedFDeriv ℝ (n+1) (S ∘ X) z v) t-
        fderiv ℝ b (X z t) ((iteratedFDeriv ℝ (n+1) X z v) t) := by
    dsimp only [S]
    rw [path_composition_derivative b hb.continuous X (hS.comp hX)]
    let ev : C(K,E) →L[ℝ] E := ContinuousMap.evalCLM ℝ t
    have hXt : ContDiff ℝ ∞ (fun y => X y t) := ev.contDiff.comp hX
    rw [higher_chain_linear_split _ b hXt hb,path_derivative_evaluation X hX]
    abel
  simp_rw [he]
  exact (iteratedFDeriv ℝ (n+1) (S ∘ X) z v).continuous.sub
    (((hb.continuous_fderiv (by simp)).comp (X z).continuous).clm_apply
      (iteratedFDeriv ℝ (n+1) X z v).continuous)
end Asakura.Chapter12
#print axioms Asakura.Chapter12.path_remainder_continuous

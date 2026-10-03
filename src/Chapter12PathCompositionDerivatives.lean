import Chapter12SuperpositionHigherBounds

open scoped ContDiff Topology
namespace Asakura.Chapter12
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

theorem path_composition_derivative {K E G : Type*}
    [TopologicalSpace K] [CompactSpace K]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (b : E → E) (hb : Continuous b)
    (X : G → C(K,E))
    (hY : ContDiff ℝ ∞ ((continuousMapSuperposition b hb) ∘ X))
    (k : ℕ) (z : G) (v : Fin k → G) (t : K) :
    (iteratedFDeriv ℝ k ((continuousMapSuperposition b hb) ∘ X) z v) t =
      iteratedFDeriv ℝ k (b ∘ (fun y => X y t)) z v := by
  let ev : C(K,E) →L[ℝ] E := ContinuousMap.evalCLM ℝ t
  have he : ev ∘ ((continuousMapSuperposition b hb) ∘ X)=b ∘ (fun y => X y t) := rfl
  have hh := congrArg (fun f : G → E => iteratedFDeriv ℝ k f z v) he
  rw [ev.iteratedFDeriv_comp_left hY.contDiffAt (by simp)] at hh
  exact hh
end Asakura.Chapter12
#print axioms Asakura.Chapter12.path_composition_derivative

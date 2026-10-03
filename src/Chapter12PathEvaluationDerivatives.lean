import Chapter12SuperpositionHigherBounds

open scoped ContDiff Topology
namespace Asakura.Chapter12
set_option maxHeartbeats 1200000

theorem path_evaluation_derivative_bound {K E G : Type*}
    [TopologicalSpace K] [CompactSpace K]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (X : G → C(K,E)) (hX : ContDiff ℝ ∞ X) (k : ℕ) (C : ℝ) (hC : 0≤C)
    (hb : ∀z,‖iteratedFDeriv ℝ k X z‖≤C) (z : G) (t : K) :
    ‖iteratedFDeriv ℝ k (fun y => X y t) z‖≤C := by
  have he : (fun y => X y t)=(ContinuousMap.evalCLM ℝ t) ∘ X := rfl
  rw [he,(ContinuousMap.evalCLM ℝ t).iteratedFDeriv_comp_left hX.contDiffAt (by simp)]
  apply ContinuousMultilinearMap.opNorm_le_bound hC
  intro v
  exact ((iteratedFDeriv ℝ k X z v).norm_coe_le_norm t).trans
    (((iteratedFDeriv ℝ k X z).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (hb z) (Finset.prod_nonneg (fun i _ => norm_nonneg _))))
end Asakura.Chapter12
#print axioms Asakura.Chapter12.path_evaluation_derivative_bound

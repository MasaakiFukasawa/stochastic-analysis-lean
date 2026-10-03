import Chapter12SuperpositionSmooth

open scoped Topology ContDiff BigOperators
namespace Asakura.Chapter12
universe u v
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

theorem superposition_iterated_derivative {K : Type v} {E F : Type u}
    [TopologicalSpace K] [CompactSpace K]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (hf : ContDiff ℝ ∞ f)
    (hs : ContDiff ℝ ∞ (continuousMapSuperposition (K:=K) f hf.continuous))
    (k : ℕ) (x : C(K,E)) (v : Fin k → C(K,E)) (t : K) :
    (iteratedFDeriv ℝ k (continuousMapSuperposition f hf.continuous) x v) t=
      iteratedFDeriv ℝ k f (x t) (fun i => v i t) := by
  let evE : C(K,E) →L[ℝ] E := ContinuousMap.evalCLM ℝ t
  let evF : C(K,F) →L[ℝ] F := ContinuousMap.evalCLM ℝ t
  have he : evF ∘ continuousMapSuperposition f hf.continuous=f ∘ evE := rfl
  have hh := congrArg (fun g : C(K,E) → F => iteratedFDeriv ℝ k g x v) he
  rw [evF.iteratedFDeriv_comp_left hs.contDiffAt (by simp),
    evE.iteratedFDeriv_comp_right hf x (by simp)] at hh
  exact hh

theorem superposition_higher_norm_bound {K : Type v} {E F : Type u}
    [TopologicalSpace K] [CompactSpace K]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (hf : ContDiff ℝ ∞ f)
    (hs : ContDiff ℝ ∞ (continuousMapSuperposition (K:=K) f hf.continuous))
    (k : ℕ) (C : ℝ) (hC : 0≤C) (hb : ∀ z,‖iteratedFDeriv ℝ k f z‖≤C)
    (x : C(K,E)) : ‖iteratedFDeriv ℝ k (continuousMapSuperposition f hf.continuous) x‖≤C := by
  apply ContinuousMultilinearMap.opNorm_le_bound hC
  intro v
  apply (ContinuousMap.norm_le _ (mul_nonneg hC (Finset.prod_nonneg (fun i _ => norm_nonneg _)))).mpr
  intro t
  rw [superposition_iterated_derivative f hf hs]
  exact ((iteratedFDeriv ℝ k f (x t)).le_opNorm _).trans
    (mul_le_mul (hb _) (Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => (v i).norm_coe_le_norm t))
      (Finset.prod_nonneg (fun i _ => norm_nonneg _)) hC)
end Asakura.Chapter12
#print axioms Asakura.Chapter12.superposition_higher_norm_bound

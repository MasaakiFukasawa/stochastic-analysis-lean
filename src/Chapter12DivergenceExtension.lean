import Chapter12DivergenceClosedGraph

open Filter
open scoped Topology RealInnerProductSpace
namespace Asakura.Chapter12

/-- The passage from smooth finite sums to D^{1,2}: the square estimate
constructs a divergence limit, and duality identifies it. -/
theorem divergence_extension_by_square_estimate
    {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [NormedAddCommGroup G] (D : E →ₗ.[ℝ] F)
    (u : ℕ → F) (v : ℕ → G) (z : ℕ → E) (u₀ : F) (v₀ : G)
    (hu : Tendsto u atTop (𝓝 u₀)) (hv : Tendsto v atTop (𝓝 v₀))
    (hz : ∀ n, IsDivergence D (u n) (z n))
    (hpair : ∀ n m, ‖z n-z m‖^2 ≤ ‖u n-u m‖^2+‖v n-v m‖^2)
    (hbound : ∀ n, ‖z n‖^2 ≤ ‖u n‖^2+‖v n‖^2) :
    ∃ z₀, Tendsto z atTop (𝓝 z₀) ∧ IsDivergence D u₀ z₀ ∧
      ‖z₀‖^2 ≤ ‖u₀‖^2+‖v₀‖^2 := by
  have hc : CauchySeq z := by
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    obtain ⟨N,hN⟩ := Metric.cauchySeq_iff.mp hu.cauchySeq (ε/2) (by linarith)
    obtain ⟨M,hM⟩ := Metric.cauchySeq_iff.mp hv.cauchySeq (ε/2) (by linarith)
    refine ⟨max N M,fun n hn m hm => ?_⟩
    have hun := hN n (le_trans (le_max_left _ _) hn) m (le_trans (le_max_left _ _) hm)
    have hvn := hM n (le_trans (le_max_right _ _) hn) m (le_trans (le_max_right _ _) hm)
    rw [dist_eq_norm] at hun hvn ⊢
    have hu2 : ‖u n-u m‖^2 < (ε/2)^2 :=
      (sq_lt_sq₀ (norm_nonneg _) (by linarith)).mpr hun
    have hv2 : ‖v n-v m‖^2 < (ε/2)^2 :=
      (sq_lt_sq₀ (norm_nonneg _) (by linarith)).mpr hvn
    have hb := hpair n m
    nlinarith [norm_nonneg (z n-z m)]
  obtain ⟨z₀,hz₀⟩ := cauchySeq_tendsto_of_complete hc
  refine ⟨z₀,hz₀,divergence_closed D hz hu hz₀,?_⟩
  exact le_of_tendsto_of_tendsto (hz₀.norm.pow 2) ((hu.norm.pow 2).add (hv.norm.pow 2))
    (Filter.Eventually.of_forall hbound)

end Asakura.Chapter12

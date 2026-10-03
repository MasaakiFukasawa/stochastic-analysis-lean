import Chapter12DivergenceExtension

open Set Filter
open scoped Topology RealInnerProductSpace
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000

/-- The square estimate extends from a linear cylinder graph to its actual
closure. Difference estimates follow from duality and uniqueness, rather
than being supplied separately for a chosen approximation. -/
theorem divergence_square_on_graph_closure {E F G : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (D : E →ₗ.[ℝ] F) (hd : DenseRange (fun f : D.domain => (f : E)))
    (V : Submodule ℝ (F×G))
    (hcore : ∀ a∈V,∃ z,IsDivergence D a.1 z ∧ ‖z‖^2≤‖a.1‖^2+‖a.2‖^2)
    (a : F×G) (ha : a∈V.topologicalClosure) :
    ∃ z,IsDivergence D a.1 z ∧ ‖z‖^2≤‖a.1‖^2+‖a.2‖^2 := by
  obtain ⟨b,hb,hbt⟩ := mem_closure_iff_seq_limit.mp ha
  choose z hz hzbound using (fun n => hcore (b n) (hb n))
  have hdiff (n m : ℕ) : ‖z n-z m‖^2≤‖(b n).1-(b m).1‖^2+‖(b n).2-(b m).2‖^2 := by
    obtain ⟨w,hw,hwb⟩ := hcore (b n-b m) (V.sub_mem (hb n) (hb m))
    have hh : IsDivergence D ((b n).1-(b m).1) (z n-z m) := by
      intro x
      rw [inner_sub_right,inner_sub_right,hz n x,hz m x]
    have he := divergence_unique D hd hh hw
    simpa only [← he,Prod.fst_sub,Prod.snd_sub] using hwb
  obtain ⟨z₀,_,hz₀,hbound⟩ := divergence_extension_by_square_estimate D
    (fun n => (b n).1) (fun n => (b n).2) z a.1 a.2
    (continuous_fst.tendsto a |>.comp hbt) (continuous_snd.tendsto a |>.comp hbt)
    hz hdiff hzbound
  exact ⟨z₀,hz₀,hbound⟩

end Asakura.Chapter12

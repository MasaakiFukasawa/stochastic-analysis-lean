import Chapter12PolygonalUniform

open Set Filter
open scoped Topology
namespace Asakura.Chapter12

/-- Any choice of enclosing mesh endpoints is sufficient; no nesting of
partitions is used in the uniform approximation argument. -/
theorem mesh_endpoint_uniform (T : ℝ)
    (l : ℕ → Icc (0:ℝ) T → Icc (0:ℝ) T)
    (h : ℕ → ℝ) (hh : Tendsto h atTop (𝓝 0))
    (hb : ∀ n t,|((l n t):ℝ)-(t:ℝ)|≤h n) :
    TendstoUniformly l id atTop := by
  apply Metric.tendstoUniformly_iff.mpr
  intro e he
  filter_upwards [hh.eventually (gt_mem_nhds he)] with n hn
  intro t
  have hd : dist (id t) (l n t)=|((l n t):ℝ)-(t:ℝ)| := by
    simp only [id_eq,Subtype.dist_eq,Real.dist_eq,abs_sub_comm]
  rw [hd]
  exact (hb n t).trans_lt hn

theorem polygonal_mesh_uniform {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : ℝ) (f : Icc (0:ℝ) T → E) (hf : Continuous f)
    (l r : ℕ → Icc (0:ℝ) T → Icc (0:ℝ) T)
    (a : ℕ → Icc (0:ℝ) T → ℝ) (ha : ∀ n t,0≤a n t ∧ a n t≤1)
    (h : ℕ → ℝ) (hh : Tendsto h atTop (𝓝 0))
    (hb : ∀ n t,((l n t):ℝ)≤t ∧ (t:ℝ)≤r n t ∧ ((r n t):ℝ)-l n t≤h n) :
    TendstoUniformly (fun n t => (1-a n t) • f (l n t)+a n t • f (r n t)) f atTop := by
  apply polygonal_uniform_convergence T f hf l r a ha
  · apply mesh_endpoint_uniform T l h hh
    intro n t
    rw [abs_of_nonpos (sub_nonpos.mpr (hb n t).1)]
    linarith [(hb n t).2.1,(hb n t).2.2]
  · apply mesh_endpoint_uniform T r h hh
    intro n t
    rw [abs_of_nonneg (sub_nonneg.mpr (hb n t).2.1)]
    linarith [(hb n t).1,(hb n t).2.2]

end Asakura.Chapter12

import Chapter12DivergenceSquareClosure

open Set Filter
open scoped Topology
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

/-- A bounded linear relation on a core extends over the closure of its
input space. Its output is constructed as a Cauchy limit. -/
theorem bounded_relation_extends_closure {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (V : Submodule ℝ (E×F)) (C : ℝ) (hC : 0≤C)
    (hb : ∀ a∈V,‖a.2‖≤C*‖a.1‖)
    (x : E) (hx : x∈closure ((Prod.fst : E×F → E) '' (V : Set (E×F)))) :
    ∃ y : F,(x,y)∈V.topologicalClosure ∧ ‖y‖≤C*‖x‖ := by
  obtain ⟨a,ha,hat⟩ := mem_closure_iff_seq_limit.mp hx
  choose b hbmem hba using ha
  have hbt : Tendsto (fun n => (b n).1) atTop (𝓝 x) := by simpa only [hba] using hat
  have hc : CauchySeq (fun n => (b n).2) := by
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    obtain ⟨N,hN⟩ := Metric.cauchySeq_iff.mp hbt.cauchySeq (ε/(C+1)) (div_pos hε (by linarith))
    refine ⟨N,fun n hn m hm => ?_⟩
    have hd := hN n hn m hm
    have hh := hb (b n-b m) (V.sub_mem (hbmem n) (hbmem m))
    simp only [Prod.fst_sub,Prod.snd_sub] at hh
    rw [dist_eq_norm] at hd ⊢
    calc
      ‖(b n).2-(b m).2‖≤C*‖(b n).1-(b m).1‖ := hh
      _≤(C+1)*‖(b n).1-(b m).1‖ := mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
      _<(C+1)*(ε/(C+1)) := mul_lt_mul_of_pos_left hd (by linarith)
      _=ε := by field_simp
  obtain ⟨y,hy⟩ := cauchySeq_tendsto_of_complete hc
  refine ⟨y,?_,?_⟩
  · exact V.isClosed_topologicalClosure.mem_of_tendsto (hbt.prodMk_nhds hy)
      (Eventually.of_forall (fun n => V.le_topologicalClosure (hbmem n)))
  · exact le_of_tendsto_of_tendsto hy.norm (tendsto_const_nhds.mul hbt.norm)
      (Eventually.of_forall (fun n => hb (b n) (hbmem n)))

end Asakura.Chapter12

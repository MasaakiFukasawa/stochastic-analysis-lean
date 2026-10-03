import Chapter12ScaleGraphRaw

open MeasureTheory Set
open scoped ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

theorem finite_sum_derivative_graph_raw {Ω H ι : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [Fintype ι]
    (P : Measure Ω) (p : ℝ≥0∞) [Fact (1≤p)]
    (D : Lp ℝ p P →ₗ.[ℝ] Lp H p P)
    (F : ι → Ω → ℝ) (U : ι → Ω → H)
    (hF : ∀ i,MemLp (F i) p P) (hU : ∀ i,MemLp (U i) p P)
    (hFU : ∀ i,((hF i).toLp _,(hU i).toLp _) ∈ D.graph) :
    ∃ hi : MemLp (fun w => ∑ i,F i w) p P,
    ∃ hdi : MemLp (fun w => ∑ i,U i w) p P,
      (hi.toLp _,hdi.toLp _) ∈ D.graph := by
  classical
  have hi : MemLp (fun w => ∑ i,F i w) p P := by
    convert memLp_finsetSum' Finset.univ (fun i _ => hF i) using 1
    funext w
    exact (Finset.sum_apply w Finset.univ F).symm
  have hdi : MemLp (fun w => ∑ i,U i w) p P := by
    convert memLp_finsetSum' Finset.univ (fun i _ => hU i) using 1
    funext w
    exact (Finset.sum_apply w Finset.univ U).symm
  have hg := D.graph.sum_mem (fun i (_ : i∈Finset.univ) => hFU i)
  have hv : (∑ i,(hF i).toLp _) = hi.toLp _ := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ (fun i => (hF i).toLp _),
      ae_all_iff.mpr (fun i => (hF i).coeFn_toLp),hi.coeFn_toLp] with w hw hf hh
    rw [hw,hh]
    exact Finset.sum_congr rfl (fun i _ => hf i)
  have hu : (∑ i,(hU i).toLp _) = hdi.toLp _ := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ (fun i => (hU i).toLp _),
      ae_all_iff.mpr (fun i => (hU i).coeFn_toLp),hdi.coeFn_toLp] with w hw hf hh
    rw [hw,hh]
    exact Finset.sum_congr rfl (fun i _ => hf i)
  refine ⟨hi,hdi,?_⟩
  change (∑ i,((hF i).toLp _,(hU i).toLp _)) ∈ D.graph at hg
  have he : (∑ i,((hF i).toLp _,(hU i).toLp _)) = (hi.toLp _,hdi.toLp _) := by
    apply Prod.ext
    · simpa only [Prod.fst_sum] using hv
    · simpa only [Prod.snd_sum] using hu
  rwa [he] at hg

end Asakura.Chapter12

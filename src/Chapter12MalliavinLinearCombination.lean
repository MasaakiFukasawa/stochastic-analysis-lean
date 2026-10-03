import Chapter12FiniteSumGraphRaw

open MeasureTheory Set
open scoped ENNReal
namespace Asakura.Chapter12
set_option maxHeartbeats 1600000

theorem malliavin_linear_combination {Ω H I:Type*} [MeasurableSpace Ω] [Fintype I]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (P:Measure Ω) (D:Lp ℝ 2 P →ₗ.[ℝ] Lp H 2 P)
    (F:I → Lp ℝ 2 P) (U:I → Lp H 2 P) (hFU:∀i,(F i,U i)∈D.graph) (a:I → ℝ) :
    ∃(X:Lp ℝ 2 P) (V:Lp H 2 P), (X,V)∈D.graph ∧
      (X:Ω → ℝ)=ᵐ[P] (fun w => ∑i,a i*F i w) ∧
      (V:Ω → H)=ᵐ[P] (fun w => ∑i,a i • U i w) := by
  classical
  refine ⟨∑i,a i • F i,∑i,a i • U i,?_,?_,?_⟩
  · have hh := D.graph.sum_mem (fun i (_:i∈Finset.univ) => D.graph.smul_mem (a i) (hFU i))
    have he : (∑i,a i • (F i,U i))=(∑i,a i • F i,∑i,a i • U i) := by
      apply Prod.ext <;> simp [Prod.fst_sum,Prod.snd_sum]
    rwa [he] at hh
  · filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ (fun i => a i • F i),
      ae_all_iff.mpr (fun i => Lp.coeFn_smul (a i) (F i))] with w hw hs
    rw [hw]
    exact Finset.sum_congr rfl (fun i _ => by rw [hs i];rfl)
  · filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ (fun i => a i • U i),
      ae_all_iff.mpr (fun i => Lp.coeFn_smul (a i) (U i))] with w hw hs
    rw [hw]
    exact Finset.sum_congr rfl (fun i _ => by rw [hs i];rfl)
end Asakura.Chapter12
#print axioms Asakura.Chapter12.malliavin_linear_combination

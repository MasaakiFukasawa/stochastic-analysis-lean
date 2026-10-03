import Chapter12DivergenceClosedGraph
import Mathlib.MeasureTheory.Function.L2Space

open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

theorem divergence_finite_sum_raw {Ω H ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (P : Measure Ω) (D : Lp ℝ 2 P →ₗ.[ℝ] Lp H 2 P)
    (u : ι → Ω → H) (z : ι → Ω → ℝ)
    (hu : ∀ i,MemLp (u i) 2 P) (hz : ∀ i,MemLp (z i) 2 P)
    (hd : ∀ i,IsDivergence D ((hu i).toLp _) ((hz i).toLp _)) :
    ∃ (hU : MemLp (fun w => ∑ i,u i w) 2 P) (hZ : MemLp (fun w => ∑ i,z i w) 2 P),
      IsDivergence D (hU.toLp _) (hZ.toLp _) := by
  classical
  have hU := memLp_finsetSum Finset.univ (fun i _ => hu i)
  have hZ := memLp_finsetSum Finset.univ (fun i _ => hz i)
  have heU : hU.toLp _=∑ i,(hu i).toLp _ := by
    apply Lp.ext
    filter_upwards [hU.coeFn_toLp,Lp.coeFn_fun_finsetSum Finset.univ (fun i => (hu i).toLp _),
      ae_all_iff.mpr (fun i => (hu i).coeFn_toLp)] with w hw hs hi
    rw [hw,hs]
    exact Finset.sum_congr rfl (fun i _ => (hi i).symm)
  have heZ : hZ.toLp _=∑ i,(hz i).toLp _ := by
    apply Lp.ext
    filter_upwards [hZ.coeFn_toLp,Lp.coeFn_fun_finsetSum Finset.univ (fun i => (hz i).toLp _),
      ae_all_iff.mpr (fun i => (hz i).coeFn_toLp)] with w hw hs hi
    rw [hw,hs]
    exact Finset.sum_congr rfl (fun i _ => (hi i).symm)
  refine ⟨hU,hZ,?_⟩
  rw [heU,heZ]
  intro f
  simp only [inner_sum]
  exact Finset.sum_congr rfl (fun i _ => hd i f)

theorem divergence_smul_raw {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (P : Measure Ω) (D : Lp ℝ 2 P →ₗ.[ℝ] Lp H 2 P)
    (u : Ω → H) (z : Ω → ℝ) (hu : MemLp u 2 P) (hz : MemLp z 2 P)
    (hd : IsDivergence D (hu.toLp _) (hz.toLp _)) (a : ℝ) :
    ∃ (hU : MemLp (fun w => a • u w) 2 P) (hZ : MemLp (fun w => a*z w) 2 P),
      IsDivergence D (hU.toLp _) (hZ.toLp _) := by
  have hU : MemLp (fun w => a • u w) 2 P := hu.const_smul a
  have hZ : MemLp (fun w => a*z w) 2 P := hz.const_smul a
  have heU : hU.toLp _=a • hu.toLp _ := by
    apply Lp.ext
    filter_upwards [hU.coeFn_toLp,Lp.coeFn_smul a (hu.toLp _),hu.coeFn_toLp] with w h1 h2 h3
    rw [h1,h2]
    change a • u w=a • hu.toLp _ w
    rw [h3]
  have heZ : hZ.toLp _=a • hz.toLp _ := by
    apply Lp.ext
    filter_upwards [hZ.coeFn_toLp,Lp.coeFn_smul a (hz.toLp _),hz.coeFn_toLp] with w h1 h2 h3
    rw [h1,h2]
    change a*z w=a*hz.toLp _ w
    rw [h3]
  refine ⟨hU,hZ,?_⟩
  rw [heU,heZ]
  intro f
  rw [real_inner_smul_right,real_inner_smul_right,hd]

end Asakura.Chapter12

import Chapter12DivergenceClosedGraph
import Mathlib.MeasureTheory.Function.L2Space

open MeasureTheory Set
open scoped RealInnerProductSpace
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

/-- Raw integral form of the already constructed adjoint on one actual
derivative-graph pair. -/
theorem divergence_pairing_raw {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (P : Measure Ω) (D : Lp ℝ 2 P →ₗ.[ℝ] Lp H 2 P)
    (F Z : Ω → ℝ) (V U : Ω → H)
    (hF : MemLp F 2 P) (hZ : MemLp Z 2 P) (hV : MemLp V 2 P) (hU : MemLp U 2 P)
    (hFV : (hF.toLp _,hV.toLp _)∈D.graph)
    (hUZ : IsDivergence D (hU.toLp _) (hZ.toLp _)) :
    (∫ w,inner ℝ (V w) (U w) ∂P)=∫ w,F w*Z w ∂P := by
  obtain ⟨f,hf,hDf⟩ := D.mem_graph_iff.mp hFV
  have hh := hUZ f
  rw [hf,hDf,L2.inner_def,L2.inner_def] at hh
  have hleft : (∫ w,inner ℝ (hV.toLp _ w) (hU.toLp _ w) ∂P)=∫ w,inner ℝ (V w) (U w) ∂P := by
    apply integral_congr_ae
    filter_upwards [hV.coeFn_toLp,hU.coeFn_toLp] with w hv hu
    rw [hv,hu]
  have hright : (∫ w,inner ℝ (hF.toLp _ w) (hZ.toLp _ w) ∂P)=∫ w,F w*Z w ∂P := by
    apply integral_congr_ae
    filter_upwards [hF.coeFn_toLp,hZ.coeFn_toLp] with w hf hz
    rw [hf,hz]
    simp [RCLike.inner_apply,mul_comm]
  exact hleft.symm.trans (hh.trans hright)

end Asakura.Chapter12

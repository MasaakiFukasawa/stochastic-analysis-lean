import Mathlib.Topology.Algebra.Module.LinearPMap
import Chapter12Representation
import Mathlib.Topology.Sequences

open Filter Set
open scoped Topology
namespace Asakura.Chapter12

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Integration by parts supplies continuous test functionals on the two
spaces. If the tests separate derivative limits, the derivative is closable.
No boundedness estimate for the derivative is used. -/
theorem closable_of_duality (D : E →ₗ.[ℝ] F) {ι : Type*}
    (left : ι → F →L[ℝ] ℝ) (right : ι → E →L[ℝ] ℝ)
    (hdual : ∀ i x, left i (D x) = right i x)
    (hsep : ∀ y, (∀ i, left i y = 0) → y = 0) : D.IsClosable := by
  refine ⟨D.graph.topologicalClosure.toLinearPMap, ?_⟩
  symm
  apply Submodule.toLinearPMap_graph_eq
  intro z hz hz0
  apply hsep
  intro i
  have hclosed : IsClosed {z : E × F | left i z.2 = right i z.1} :=
    isClosed_eq ((left i).continuous.comp continuous_snd)
      ((right i).continuous.comp continuous_fst)
  have hsub : (D.graph : Set (E × F)) ⊆ {z | left i z.2 = right i z.1} := by
    intro z hz
    obtain ⟨x, hx, hy⟩ := D.mem_graph_iff.mp hz
    change left i z.2 = right i z.1
    rw [← hx, ← hy]
    exact hdual i x
  have he := closure_minimal hsub hclosed hz
  change left i z.2 = right i z.1 at he
  simpa only [hz0, map_zero] using he

/-- Both value and derivative are limits in the graph closure; the derivative
limit is unique. This is the independence of the approximating sequence. -/
theorem derivative_limit_unique (D : E →ₗ.[ℝ] F) (hc : D.IsClosable)
    {x : E} {u v : F} {a b : ℕ → D.domain}
    (ha : Tendsto (fun n => ((a n : E), D (a n))) atTop (𝓝 (x,u)))
    (hb : Tendsto (fun n => ((b n : E), D (b n))) atTop (𝓝 (x,v))) : u = v := by
  have hu : (x,u) ∈ D.graph.topologicalClosure :=
    mem_closure_of_tendsto ha (Filter.Eventually.of_forall fun n => D.mem_graph (a n))
  have hv : (x,v) ∈ D.graph.topologicalClosure :=
    mem_closure_of_tendsto hb (Filter.Eventually.of_forall fun n => D.mem_graph (b n))
  rw [hc.graph_closure_eq_closure_graph] at hu hv
  obtain ⟨a, ha, hau⟩ := D.closure.mem_graph_iff.mp hu
  obtain ⟨b, hb, hbv⟩ := D.closure.mem_graph_iff.mp hv
  have hab : a = b := Subtype.ext (ha.trans hb.symm)
  subst b
  exact hau.symm.trans hbv

/-- The jointly closed extension, unlike a bounded extension on E, retains
control of both coordinates. -/
theorem derivative_graph_closed (D : E →ₗ.[ℝ] F) (hc : D.IsClosable) :
    IsClosed (D.closure.graph : Set (E × F)) := hc.closure_isClosed

/-- Completeness belongs to the closed graph (value and derivative together). -/
theorem derivative_graph_complete [CompleteSpace E] [CompleteSpace F]
    (D : E →ₗ.[ℝ] F) (hc : D.IsClosable) :
    CompleteSpace D.closure.graph :=
  (derivative_graph_closed D hc).isComplete.completeSpace_coe

end Asakura.Chapter12

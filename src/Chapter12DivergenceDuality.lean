import Chapter12GraphClosure
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Operator.Extend

open Filter Set
open scoped Topology RealInnerProductSpace
namespace Asakura.Chapter12
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The divergence is specified by testing against the original smooth
core, not by assuming that the derivative is a bounded operator. -/
def IsDivergence (D : E →ₗ.[ℝ] F) (u : F) (z : E) : Prop :=
  ∀ x : D.domain, ⟪D x,u⟫ = ⟪(x : E),z⟫

theorem divergence_unique (D : E →ₗ.[ℝ] F)
    (hd : DenseRange (fun x : D.domain => (x : E))) {u : F} {z w : E}
    (hz : IsDivergence D u z) (hw : IsDivergence D u w) : z = w := by
  have he : ∀ x : E, ⟪x,z⟫ = ⟪x,w⟫ := by
    exact isClosed_property hd (isClosed_eq (by fun_prop) (by fun_prop))
      (fun x => (hz x).symm.trans (hw x))
  exact ext_inner_left ℝ he

/-- The manuscript's closedness argument is just passage to limits in each
continuous pairing. -/
theorem divergence_closed (D : E →ₗ.[ℝ] F) {u : ℕ → F} {z : ℕ → E}
    {u₀ : F} {z₀ : E} (h : ∀ n, IsDivergence D (u n) (z n))
    (hu : Tendsto u atTop (𝓝 u₀)) (hz : Tendsto z atTop (𝓝 z₀)) :
    IsDivergence D u₀ z₀ := by
  intro x
  exact tendsto_nhds_unique
    ((tendsto_const_nhds.inner hu).congr (fun n => h n x))
    (tendsto_const_nhds.inner hz)

/-- The duality also holds on the joint closure of the derivative graph. -/
theorem divergence_on_closed_derivative (D : E →ₗ.[ℝ] F) (hc : D.IsClosable)
    {u : F} {z : E} (h : IsDivergence D u z) :
    IsDivergence D.closure u z := by
  intro x
  have hs : IsClosed {p : E × F | ⟪p.2,u⟫ = ⟪p.1,z⟫} :=
    isClosed_eq (by fun_prop) (by fun_prop)
  have hsub : (D.graph : Set (E × F)) ⊆ {p | ⟪p.2,u⟫ = ⟪p.1,z⟫} := by
    intro p hp
    obtain ⟨y,hy,hy'⟩ := D.mem_graph_iff.mp hp
    change ⟪p.2,u⟫ = ⟪p.1,z⟫
    rw [← hy, ← hy']
    exact h y
  have hx := D.closure.mem_graph x
  rw [← hc.graph_closure_eq_closure_graph] at hx
  exact closure_minimal hsub hs hx

/-- Riesz representation of the bounded functional in the definition of
Dom(delta), using the already dense smooth core. -/
theorem divergence_exists_of_bound [CompleteSpace E] (D : E →ₗ.[ℝ] F)
    (hd : DenseRange (fun x : D.domain => (x : E))) (u : F)
    (hb : ∃ C : ℝ, ∀ x : D.domain, |⟪D x,u⟫| ≤ C * ‖(x : E)‖) :
    ∃ z, IsDivergence D u z := by
  let f : D.domain →ₗ[ℝ] ℝ :=
    { toFun := fun x => ⟪D x,u⟫
      map_add' := by intros; simp [D.map_add,inner_add_left]
      map_smul' := by intros; simp [D.map_smul,inner_smul_left] }
  let L : E →L[ℝ] ℝ := f.extendOfNorm D.domain.subtype
  refine ⟨(InnerProductSpace.toDual ℝ E).symm L, ?_⟩
  intro x
  rw [real_inner_comm ((InnerProductSpace.toDual ℝ E).symm L) (x : E),
    InnerProductSpace.toDual_symm_apply]
  symm
  apply LinearMap.extendOfNorm_eq hd
  simpa only [Real.norm_eq_abs,f,LinearMap.coe_mk,AddHom.coe_mk,
    Submodule.subtype_apply] using hb

theorem divergence_bound (D : E →ₗ.[ℝ] F) {u : F} {z : E}
    (h : IsDivergence D u z) :
    ∀ x : D.domain, |⟪D x,u⟫| ≤ ‖z‖ * ‖(x : E)‖ := by
  intro x
  rw [h x,mul_comm]
  exact abs_real_inner_le_norm _ _

end Asakura.Chapter12

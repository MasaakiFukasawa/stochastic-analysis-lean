import Chapter12DivergenceDuality

open Set Filter
open scoped Topology RealInnerProductSpace
namespace Asakura.Chapter12
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The adjoint relation used to define the divergence is linear, without
any boundedness assumption on D. -/
def divergenceGraph (D : E →ₗ.[ℝ] F) : Submodule ℝ (F × E) where
  carrier := {p | IsDivergence D p.1 p.2}
  zero_mem' := by intro x; simp
  add_mem' := by
    intro p q hp hq x
    change ⟪D x,p.1+q.1⟫ = ⟪(x:E),p.2+q.2⟫
    rw [inner_add_right,inner_add_right,hp x,hq x]
  smul_mem' := by
    intro a p hp x
    change ⟪D x,a • p.1⟫ = ⟪(x:E),a • p.2⟫
    rw [inner_smul_right,inner_smul_right,hp x]

theorem divergence_graph_isClosed (D : E →ₗ.[ℝ] F) :
    IsClosed (divergenceGraph D : Set (F × E)) := by
  have he : (divergenceGraph D : Set (F × E)) =
      ⋂ x : D.domain, {p | ⟪D x,p.1⟫ = ⟪(x:E),p.2⟫} := by
    ext p
    simp only [divergenceGraph,Submodule.coe_set_mk,Set.mem_setOf_eq,
      Set.mem_iInter,IsDivergence]
    rfl
  rw [he]
  exact isClosed_iInter fun x => isClosed_eq (by fun_prop) (by fun_prop)

noncomputable def divergenceOperator (D : E →ₗ.[ℝ] F) : F →ₗ.[ℝ] E :=
  (divergenceGraph D).toLinearPMap

theorem divergence_operator_graph (D : E →ₗ.[ℝ] F)
    (hd : DenseRange (fun x : D.domain => (x : E))) :
    (divergenceOperator D).graph = divergenceGraph D := by
  apply Submodule.toLinearPMap_graph_eq
  intro p hp hp0
  apply divergence_unique D hd (u := 0)
  · change IsDivergence D p.1 p.2 at hp
    simpa only [hp0] using hp
  · intro x
    simp

theorem divergence_operator_closed (D : E →ₗ.[ℝ] F)
    (hd : DenseRange (fun x : D.domain => (x : E))) :
    (divergenceOperator D).IsClosed := by
  unfold LinearPMap.IsClosed
  rw [divergence_operator_graph D hd]
  exact divergence_graph_isClosed D

/-- The definition by a bounded functional and the definition by a dual
L2 element coincide. -/
theorem divergence_domain_iff [CompleteSpace E] (D : E →ₗ.[ℝ] F)
    (hd : DenseRange (fun x : D.domain => (x : E))) (u : F) :
    (∃ z, IsDivergence D u z) ↔
      ∃ C : ℝ, ∀ x : D.domain, |⟪D x,u⟫| ≤ C*‖(x:E)‖ := by
  constructor
  · rintro ⟨z,hz⟩
    exact ⟨‖z‖,divergence_bound D hz⟩
  · exact divergence_exists_of_bound D hd u

end Asakura.Chapter12

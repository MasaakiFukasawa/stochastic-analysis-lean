import Chapter12GaussianTensorCore
import Chapter12VectorCylinderClosedDerivative
import Chapter12IteratedCylinderExpressions

open MeasureTheory ProbabilityTheory Set ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000

noncomputable def iteratedVectorCylinderExpr (H : RealHilbertSpaceData)
    (c : VectorCylinderExpr H H) : (k : ℕ) → VectorCylinderExpr H (positiveMalliavinTensorPower H k)
  | 0 => c
  | k+1 => (iteratedVectorCylinderExpr H c k).differentiate

theorem partial_linear_graph_output_unique {E F : Type*}
    [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    (D : E →ₗ.[ℝ] F) {x : E} {y z : F}
    (hy : (x,y)∈D.graph) (hz : (x,z)∈D.graph) : y=z := by
  obtain ⟨a,ha,ha'⟩ := D.mem_graph_iff.mp hy
  obtain ⟨b,hb,hb'⟩ := D.mem_graph_iff.mp hz
  have hab : a=b := Subtype.ext (ha.trans hb.symm)
  exact ha'.symm.trans ((congrArg D hab).trans hb')

/-- Closed higher derivative operators act on all finite vector cylinders,
including arbitrary changes of orthonormal coordinates. -/
theorem higher_vector_core_operators {Ω : Type*} [MeasurableSpace Ω]
    (H : RealHilbertSpaceData) [Nontrivial H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀ h∈S,HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    (p q : ℝ≥0∞) [Fact (1≤p)] [Fact (1≤q)] [HolderConjugate p q]
    (hp : p≠⊤) (hq : q≠⊤)
    (hdense : DenseRange (fun c : SmoothCylinder H => c.valueLp P W S hS hcore q hq)) :
    ∃ D : ∀ k : ℕ,Lp (positiveMalliavinTensorPower H k) p P →ₗ.[ℝ]
        Lp (positiveMalliavinTensorPower H (k+1)) p P,
      (∀ k,(D k).IsClosed) ∧
      ∀ k (c : VectorCylinderExpr H (positiveMalliavinTensorPower H k)),
        (c.valueLp P W S hS hcore p hp,c.differentiate.valueLp P W S hS hcore p hp)∈(D k).graph := by
  have h (k : ℕ) := vector_cylinder_closed_derivative (E:=positiveMalliavinTensorPower H k)
    P W S hS hcore p q hp hq hdense
  choose A hgraph hclos hclosed hterm using h
  refine ⟨fun k => (A k).closure,hclosed,fun k c => ?_⟩
  exact vector_expression_derivative_in_graph P W S hS hcore p hp (A k).closure (hterm k) c

/-- Equality of the zeroth coordinate forces equality at every derivative
order. Thus rebasing does not assume invariance of higher derivatives. -/
theorem closed_jet_all_orders_unique
    (E : ℕ → Type*) [∀ k,AddCommGroup (E k)] [∀ k,Module ℝ (E k)]
    (D : ∀ k,E k →ₗ.[ℝ] E (k+1)) (x y : ∀ k,E k)
    (hx : ∀ k,(x k,x (k+1))∈(D k).graph)
    (hy : ∀ k,(y k,y (k+1))∈(D k).graph) (h0 : x 0=y 0) : ∀ k,x k=y k := by
  intro k
  induction k with
  | zero => exact h0
  | succ k ih =>
    apply partial_linear_graph_output_unique (D k) (hx k)
    rw [ih]
    exact hy k

end Asakura.Chapter12

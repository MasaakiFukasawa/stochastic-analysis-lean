import Chapter12ScalarGradientExpression
import Chapter12VectorCylinderClosedDerivative

open MeasureTheory ProbabilityTheory Set ENNReal TopologicalSpace
open scoped Topology
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

/-- All higher derivative operators are constructed from the same scalar
Gaussian core. Successive derivatives of every cylinder lie in their graphs. -/
theorem higher_closed_cylinder_derivatives {Ω : Type*} [MeasurableSpace Ω]
    (H : RealHilbertSpaceData) [Nontrivial H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀ h∈S,HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    (p q : ℝ≥0∞) [Fact (1≤p)] [Fact (1≤q)] [HolderConjugate p q]
    (hp : p≠⊤) (hq : q≠⊤)
    (hdense : DenseRange (fun c : SmoothCylinder H => c.valueLp P W S hS hcore q hq)) :
    ∀ n : ℕ,∃ D : Lp (positiveMalliavinTensorPower H n) p P →ₗ.[ℝ]
        Lp (positiveMalliavinTensorPower H (n+1)) p P,
      D.IsClosed ∧ ∀ c : SmoothCylinder H,
        ((iteratedCylinderExpr H c n).valueLp P W S hS hcore p hp,
         (iteratedCylinderExpr H c (n+1)).valueLp P W S hS hcore p hp)∈D.graph := by
  intro n
  obtain ⟨D,hgraph,hclos,hclosed,hterm⟩ :=
    vector_cylinder_closed_derivative (E := positiveMalliavinTensorPower H n)
      P W S hS hcore p q hp hq hdense
  refine ⟨D.closure,hclosed,fun c => ?_⟩
  exact vector_expression_derivative_in_graph P W S hS hcore p hp D.closure hterm
    (iteratedCylinderExpr H c n)

/-- The scalar first derivative agrees with the first level of the
explicit iterated cylinder construction, avoiding a second definition of D. -/
theorem first_closed_cylinder_derivative {Ω : Type*} [MeasurableSpace Ω]
    (H : RealHilbertSpaceData) [Nontrivial H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀ h∈S,HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    (p : ℝ≥0∞) [Fact (1≤p)] (hp : p≠⊤)
    (D : Lp ℝ p P →ₗ.[ℝ] Lp H p P)
    (hD : ∀ c : SmoothCylinder H,(c.valueLp P W S hS hcore p hp,
      c.gradientLp P W S hS hcore p hp)∈D.graph) (c : SmoothCylinder H) :
    (c.valueLp P W S hS hcore p hp,
      (iteratedCylinderExpr H c 0).valueLp P W S hS hcore p hp)∈D.graph := by
  change (_, (cylinderFirstGradientExpr c).valueLp P W S hS hcore p hp)∈D.graph
  rw [scalar_gradient_expression]
  exact hD c

end Asakura.Chapter12

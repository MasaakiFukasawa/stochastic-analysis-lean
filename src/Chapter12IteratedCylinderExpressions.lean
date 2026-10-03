import Chapter12VectorCylinderDifferentiation
import Chapter12MalliavinTensorPowers

open MeasureTheory ProbabilityTheory Set ENNReal
open scoped Topology
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

noncomputable def cylinderFirstGradientExpr {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] (c : SmoothCylinder H) :
    VectorCylinderExpr H H :=
  .sum c.dim (fun j => .term (partialSmoothCylinder c j) (c.direction j))

noncomputable def iteratedCylinderExpr (H : RealHilbertSpaceData) (c : SmoothCylinder H) :
    (n : ℕ) → VectorCylinderExpr H (positiveMalliavinTensorPower H n)
  | 0 => cylinderFirstGradientExpr c
  | n+1 => (iteratedCylinderExpr H c n).differentiate

variable {Ω H E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Nontrivial H]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (P : Measure Ω) [IsProbabilityMeasure P]
  (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
  (hcore : ∀ h∈S,HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
  (p : ℝ≥0∞) [Fact (1≤p)] (hp : p≠⊤)

theorem vector_expression_in_graph
    (D : Lp E p P →ₗ.[ℝ] Lp (CompletedHilbertTensor H E) p P)
    (hterm : ∀ c e,(vectorCylinderValue P W S hS hcore c e p hp,
      vectorCylinderDerivative P W S hS hcore c e p hp)∈D.graph)
    (c : VectorCylinderExpr H E) :
    (c.valueLp P W S hS hcore p hp,c.gradientLp P W S hS hcore p hp)∈D.graph := by
  induction c with
  | term c e => exact hterm c e
  | sum n c ih =>
    have hh := D.graph.sum_mem (fun i (_ : i∈(Finset.univ : Finset (Fin n))) => ih i)
    simpa only [VectorCylinderExpr.valueLp,VectorCylinderExpr.gradientLp,← prod_mk_sum] using hh
  | smul a c ih => exact D.graph.smul_mem a ih

theorem vector_expression_derivative_in_graph
    (D : Lp E p P →ₗ.[ℝ] Lp (CompletedHilbertTensor H E) p P)
    (hterm : ∀ c e,(vectorCylinderValue P W S hS hcore c e p hp,
      vectorCylinderDerivative P W S hS hcore c e p hp)∈D.graph)
    (c : VectorCylinderExpr H E) :
    (c.valueLp P W S hS hcore p hp,c.differentiate.valueLp P W S hS hcore p hp)∈D.graph := by
  rw [vector_cylinder_differentiate_value]
  exact vector_expression_in_graph P W S hS hcore p hp D hterm c

end Asakura.Chapter12

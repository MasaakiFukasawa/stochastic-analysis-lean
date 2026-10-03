import Chapter12TensorCylinderPairs
import Chapter12CylinderPartialDerivative

open MeasureTheory ProbabilityTheory Set ENNReal
open scoped Topology
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

/-- Finite Hilbert-valued sums, with no choice of an infinite basis. -/
inductive VectorCylinderExpr (H E : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  | term (c : SmoothCylinder H) (e : E)
  | sum (n : ℕ) (c : Fin n → VectorCylinderExpr H E)
  | smul (a : ℝ) (c : VectorCylinderExpr H E)

noncomputable def VectorCylinderExpr.differentiate {H E : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    VectorCylinderExpr H E → VectorCylinderExpr H (CompletedHilbertTensor H E)
  | .term c e => .sum c.dim (fun j => .term (partialSmoothCylinder c j) (hilbertPureTensor (c.direction j) e))
  | .sum n c => .sum n (fun i => (c i).differentiate)
  | .smul a c => .smul a c.differentiate

variable {Ω H E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Nontrivial H]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (P : Measure Ω) [IsProbabilityMeasure P]
  (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
  (hcore : ∀ h∈S,HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
  (p : ℝ≥0∞) [Fact (1≤p)] (hp : p≠⊤)

noncomputable def VectorCylinderExpr.valueLp : VectorCylinderExpr H E → Lp E p P
  | .term c e => vectorCylinderValue P W S hS hcore c e p hp
  | .sum n c => ∑ i : Fin n,(c i).valueLp
  | .smul a c => a • c.valueLp

noncomputable def VectorCylinderExpr.gradientLp : VectorCylinderExpr H E → Lp (CompletedHilbertTensor H E) p P
  | .term c e => vectorCylinderDerivative P W S hS hcore c e p hp
  | .sum n c => ∑ i : Fin n,(c i).gradientLp
  | .smul a c => a • c.gradientLp

end Asakura.Chapter12

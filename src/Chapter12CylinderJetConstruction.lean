import Chapter12HigherClosedDerivatives
import Chapter12SobolevJetCompletion

open MeasureTheory ProbabilityTheory Set ENNReal TopologicalSpace
open scoped Topology
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

noncomputable def scalarHilbertData : RealHilbertSpaceData where
  carrier := ℝ
  normed := inferInstance
  inner := inferInstance
  complete := inferInstance
  separable := inferInstance

noncomputable def malliavinTensorOrder (H : RealHilbertSpaceData) : ℕ → RealHilbertSpaceData
  | 0 => scalarHilbertData
  | n+1 => positiveMalliavinTensorPower H n

/-- All coordinates are actual derivatives of the same scalar cylinder. -/
noncomputable def cylinderJetCoordinate {Ω : Type*} [MeasurableSpace Ω]
    (H : RealHilbertSpaceData) [Nontrivial H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀ h∈S,HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    (p : ℝ≥0∞) [Fact (1≤p)] (hp : p≠⊤) (c : SmoothCylinder H) :
    ∀ n,Lp (malliavinTensorOrder H n) p P
  | 0 => c.valueLp P W S hS hcore p hp
  | n+1 => (iteratedCylinderExpr H c n).valueLp P W S hS hcore p hp

/-- The closed scalar derivative and the constructed higher tensor
 derivatives form a single compatible family on the original cylinder core. -/
theorem cylinder_jet_closed_operators {Ω : Type*} [MeasurableSpace Ω]
    (H : RealHilbertSpaceData) [Nontrivial H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀ h∈S,HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    (p q : ℝ≥0∞) [Fact (1≤p)] [Fact (1≤q)] [HolderConjugate p q]
    (hp : p≠⊤) (hq : q≠⊤)
    (hdense : DenseRange (fun c : SmoothCylinder H => c.valueLp P W S hS hcore q hq))
    (D₀ : Lp ℝ p P →ₗ.[ℝ] Lp H p P) (hclosed : D₀.IsClosed)
    (hfirst : ∀ c : SmoothCylinder H,(c.valueLp P W S hS hcore p hp,
      c.gradientLp P W S hS hcore p hp)∈D₀.graph) :
    ∃ D : ∀ n,Lp (malliavinTensorOrder H n) p P →ₗ.[ℝ]
      Lp (malliavinTensorOrder H (n+1)) p P,
      (∀ n,(D n).IsClosed) ∧ ∀ c n,
      (cylinderJetCoordinate H P W S hS hcore p hp c n,
       cylinderJetCoordinate H P W S hS hcore p hp c (n+1))∈(D n).graph := by
  choose A hA hcoreA using higher_closed_cylinder_derivatives H P W S hS hcore p q hp hq hdense
  let D : ∀ n,Lp (malliavinTensorOrder H n) p P →ₗ.[ℝ]
      Lp (malliavinTensorOrder H (n+1)) p P
    | 0 => D₀
    | n+1 => A n
  refine ⟨D,?_,?_⟩
  · intro n
    cases n with
    | zero => exact hclosed
    | succ n => exact hA n
  · intro c n
    cases n with
    | zero => exact first_closed_cylinder_derivative H P W S hS hcore p hp D₀ hfirst c
    | succ n => exact hcoreA n c

end Asakura.Chapter12

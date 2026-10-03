import Chapter12ClosedMalliavinOperator
import Chapter12CylinderPairLinear

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

theorem closed_cylinder_graph_from_data {Ω H K : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Nontrivial H]
    [SecondCountableTopology H] [CompleteSpace H]
    [TopologicalSpace K] [FirstCountableTopology K]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀ h ∈ S, HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    (X : K → Ω → ℝ) (hXm : ∀ t, Measurable (X t))
    (hXc : ∀ w, Continuous (fun t => X t w))
    (h : K → H) (hXW : ∀ t, X t =ᵐ[P] (W (h t) : Ω → ℝ))
    (times : ℕ → K) (htimes : DenseRange times)
    (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]
    (hp : p ≠ ⊤) (hq : q ≠ ⊤)
    (hgen : ∀ f : Lp ℝ q P,
      AEStronglyMeasurable[MeasurableSpace.comap (fun w t => X t w) inferInstance] f P) :
    ∃ D : Lp ℝ p P →ₗ.[ℝ] Lp H p P, D.IsClosed ∧
      (D.graph : Set _) = closure (range (cylinderPair P W S hS hcore p hp)) := by
  obtain ⟨D,hD,hcl,_,_,hg⟩ := closed_malliavin_operator_from_wiener_data P W S hS hcore X hXm hXc h hXW
    times htimes p q hp hq hgen
  refine ⟨D.closure,hcl,?_⟩
  rw [hg,Submodule.topologicalClosure_coe]
  change closure ((Submodule.span ℝ (range (cylinderPair P W S hS hcore p hp))) : Set (Lp ℝ p P × Lp H p P)) = _
  rw [cylinderPair_span_eq_range]

end Asakura.Chapter12

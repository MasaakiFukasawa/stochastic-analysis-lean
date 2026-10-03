import Chapter12VectorHigherCore
import Chapter12CylinderJetApproximation

open MeasureTheory ProbabilityTheory Set ENNReal Filter
open scoped Topology
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000

variable {Ω : Type*} [MeasurableSpace Ω] (H : RealHilbertSpaceData) [Nontrivial H]
  (P : Measure Ω) [IsProbabilityMeasure P]
  (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
  (hcore : ∀ h∈S,HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
  (p : ℝ≥0∞) [Fact (1≤p)] (hp : p≠⊤)

noncomputable def vectorSobolevCoreJet (k : ℕ) (c : VectorCylinderExpr H H) :
    PiLp 1 (fun j : Fin (k+1) => Lp (positiveMalliavinTensorPower H j.val) p P) :=
  WithLp.toLp 1 (fun j => (iteratedVectorCylinderExpr H c j).valueLp P W S hS hcore p hp)

noncomputable def vectorSobolevJetSpace (k : ℕ) :
    Submodule ℝ (PiLp 1 (fun j : Fin (k+1) => Lp (positiveMalliavinTensorPower H j.val) p P)) :=
  (Submodule.span ℝ (range (vectorSobolevCoreJet H P W S hS hcore p hp k))).topologicalClosure

theorem vector_sobolev_core_range (k : ℕ)
    (D : ∀ k : ℕ,Lp (positiveMalliavinTensorPower H k) p P →ₗ.[ℝ]
      Lp (positiveMalliavinTensorPower H (k+1)) p P)
    (hD : ∀ k (a : VectorCylinderExpr H (positiveMalliavinTensorPower H k)),
      (a.valueLp P W S hS hcore p hp,a.differentiate.valueLp P W S hS hcore p hp)∈(D k).graph) :
    (Submodule.span ℝ (range (vectorSobolevCoreJet H P W S hS hcore p hp k)) : Set _)=
      range (vectorSobolevCoreJet H P W S hS hcore p hp k) := by
  apply jet_span_eq_range 1
    (fun j : Fin (k+1) => Lp (positiveMalliavinTensorPower H j.val) p P)
    (fun j : Fin k => D j.val) (vectorSobolevCoreJet H P W S hS hcore p hp k)
  · intro c j
    exact hD j.val (iteratedVectorCylinderExpr H c j.val)
  · refine ⟨.sum 0 Fin.elim0,?_⟩
    simp [vectorSobolevCoreJet,iteratedVectorCylinderExpr,VectorCylinderExpr.valueLp]
  · intro c d
    refine ⟨.sum 2 (Fin.cases c (fun _ => d)),?_⟩
    simp [vectorSobolevCoreJet,iteratedVectorCylinderExpr,VectorCylinderExpr.valueLp,Fin.sum_univ_two]
    rfl
  · intro a c
    exact ⟨.smul a c,rfl⟩

/-- Every completed vector Sobolev jet is approximated by finite smooth
sums in all its derivative coordinates simultaneously. -/
theorem vector_sobolev_core_approximation (k : ℕ)
    (D : ∀ k : ℕ,Lp (positiveMalliavinTensorPower H k) p P →ₗ.[ℝ]
      Lp (positiveMalliavinTensorPower H (k+1)) p P)
    (hD : ∀ k (a : VectorCylinderExpr H (positiveMalliavinTensorPower H k)),
      (a.valueLp P W S hS hcore p hp,a.differentiate.valueLp P W S hS hcore p hp)∈(D k).graph)
    (x : vectorSobolevJetSpace H P W S hS hcore p hp k) :
    ∃ c : ℕ → VectorCylinderExpr H H,
      Tendsto (fun m => vectorSobolevCoreJet H P W S hS hcore p hp k (c m)) atTop (𝓝 x.val) :=
  jet_single_core_approximation 1 _ _
    (vector_sobolev_core_range H P W S hS hcore p hp k D hD) x

end Asakura.Chapter12

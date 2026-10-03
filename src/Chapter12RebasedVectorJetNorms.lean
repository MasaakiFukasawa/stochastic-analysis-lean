import Chapter12GaussianVectorDifferenceNorm
import Chapter12FiniteVectorCoreRebasis

open MeasureTheory ProbabilityTheory Set ENNReal
namespace Asakura.Chapter12
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} [MeasurableSpace Ω]
    (H : RealHilbertSpaceData) [Nontrivial H] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀u∈S,HasLaw (W u : Ω → ℝ) (gaussianReal 0 ⟨‖u‖^2,sq_nonneg _⟩) P)
    (p q : ℝ≥0∞) [Fact (1≤p)] [Fact (1≤q)] [HolderConjugate p q]
    (hp : p≠⊤) (hq : q≠⊤)
    (hdense : DenseRange (fun c : SmoothCylinder H => c.valueLp P W S hS hcore q hq))

include hdense

theorem rebased_vector_jet_norm (c : VectorCylinderExpr H H)
    {n:ℕ} (u:Fin (n+1) → GaussianJet (n+1)) (e:Fin (n+1) → H) (he:Orthonormal ℝ e)
    (hc : c.valueLp P W S hS hcore p hp=gaussianTensorCore H P W S hS hcore p hp u e 0) (k:ℕ) :
    (fun w => ‖(iteratedVectorCylinderExpr H c k).valueLp P W S hS hcore p hp w‖)=ᵐ[P]
    (fun w => Real.sqrt (∑a:Fin k → Fin (n+1),‖iteratedFDeriv ℝ k (gaussianVectorFunction u e)
      (fun i => W (e i) w) (fun j => Pi.single (a j) 1)‖^2)) := by
  obtain ⟨D,hD,hcoreD⟩ := higher_vector_core_operators H P W S hS hcore p q hp hq hdense
  rw [vector_rebasis_all_derivatives H P W S hS hcore c p hp D hcoreD u e hc k]
  simpa only [gaussianVectorFunction_derivative_norm u e he,gaussian_tensor_array_norm] using
    gaussian_tensor_core_norm H P W S hS hcore p hp u e he k

theorem rebased_vector_jet_difference_norm (c d : VectorCylinderExpr H H)
    {n:ℕ} (u v:Fin (n+1) → GaussianJet (n+1)) (e:Fin (n+1) → H) (he:Orthonormal ℝ e)
    (hc : c.valueLp P W S hS hcore p hp=gaussianTensorCore H P W S hS hcore p hp u e 0)
    (hd : d.valueLp P W S hS hcore p hp=gaussianTensorCore H P W S hS hcore p hp v e 0) (k:ℕ) :
    (fun w => ‖((iteratedVectorCylinderExpr H c k).valueLp P W S hS hcore p hp-
      (iteratedVectorCylinderExpr H d k).valueLp P W S hS hcore p hp) w‖)=ᵐ[P]
    (fun w => Real.sqrt (∑a:Fin k → Fin (n+1),‖iteratedFDeriv ℝ k (gaussianVectorFunction u e)
      (fun i => W (e i) w) (fun j => Pi.single (a j) 1)-
      iteratedFDeriv ℝ k (gaussianVectorFunction v e) (fun i => W (e i) w) (fun j => Pi.single (a j) 1)‖^2)) := by
  obtain ⟨D,hD,hcoreD⟩ := higher_vector_core_operators H P W S hS hcore p q hp hq hdense
  rw [vector_rebasis_all_derivatives H P W S hS hcore c p hp D hcoreD u e hc k,
      vector_rebasis_all_derivatives H P W S hS hcore d p hp D hcoreD v e hd k]
  filter_upwards [Lp.coeFn_sub (gaussianTensorCore H P W S hS hcore p hp u e k)
      (gaussianTensorCore H P W S hS hcore p hp v e k),
    gaussian_tensor_core_coe H P W S hS hcore p hp u e k,
    gaussian_tensor_core_coe H P W S hS hcore p hp v e k] with w hw hu hv
  rw [hw,Pi.sub_apply,hu,hv,←Finset.sum_sub_distrib]
  simp_rw [←sub_smul]
  rw [tensor_coordinate_sum_norm H e he k,gaussian_vector_derivative_difference_norm u v e he]
end Asakura.Chapter12
#print axioms Asakura.Chapter12.rebased_vector_jet_difference_norm

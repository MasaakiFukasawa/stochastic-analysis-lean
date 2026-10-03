import Chapter12GaussianArrayNormTransport
import Chapter12GaussianHigherDivergenceLp

open MeasureTheory ProbabilityTheory Set ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4200000

/-- The high derivative estimate uses the original cylinder derivative
operators on the original probability space. -/
theorem gaussian_core_higher_bound {Ω : Type*} [MeasurableSpace Ω]
    (H : RealHilbertSpaceData) [Nontrivial H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀ h∈S,HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    {n : ℕ} (u : Fin (n+1) → GaussianJet (n+1)) (e : Fin (n+1) → H) (he : Orthonormal ℝ e)
    (p : ℕ) (hp : 0<p) [Fact (1≤((2*p:ℕ):ℝ≥0∞))]
    (q : ℝ≥0∞) [Fact (1≤q)] [HolderConjugate ((2*p:ℕ):ℝ≥0∞) q] (hq : q≠⊤)
    (hdense : DenseRange (fun c : SmoothCylinder H => c.valueLp P W S hS hcore q hq))
    (k : ℕ) :
    ‖(iteratedCylinderExpr H ((GaussianJet.divergence u).toCylinder e) k).valueLp
      P W S hS hcore (2*p:ℕ) (ENNReal.natCast_ne_top _)‖ ≤
    (k+1:ℕ)*‖gaussianTensorCore H P W S hS hcore (2*p:ℕ) (ENNReal.natCast_ne_top _) u e k‖+
    (2*(2*p-1):ℕ)*∑ j : Fin (2*p+1),
      ‖gaussianTensorCore H P W S hS hcore (2*p:ℕ) (ENNReal.natCast_ne_top _) u e (j.val+(k+1))‖ := by
  obtain ⟨D,hclosed,hD⟩ := higher_vector_core_operators H P W S hS hcore
    (2*p:ℕ) q (ENNReal.natCast_ne_top _) hq hdense
  have hnorm := gaussian_array_norm_transport H P W S hS hcore e he
    (fun b : Fin (k+1) → Fin (n+1) => (GaussianJet.divergence u).iteratedPartial (List.ofFn b))
    (2*p) (by omega)
    ((iteratedCylinderExpr H ((GaussianJet.divergence u).toCylinder e) k).valueLp
      P W S hS hcore (2*p:ℕ) (ENNReal.natCast_ne_top _))
    (gaussian_scalar_higher_core_norm H P W S hS hcore (2*p:ℕ) (ENNReal.natCast_ne_top _)
      (GaussianJet.divergence u) e he D hD k)
  rw [hnorm]
  simp_rw [gaussian_vector_core_array_norm H P W S hS hcore u e he (2*p) (by omega)]
  exact gaussian_higher_divergence_Lp_bound u p hp

end Asakura.Chapter12

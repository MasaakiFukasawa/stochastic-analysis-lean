import Chapter12GaussianScalarHigherCore
import Chapter12GaussianPartialFrechet

open MeasureTheory ProbabilityTheory Set ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

variable {Ω : Type*} [MeasurableSpace Ω] (H : RealHilbertSpaceData) [Nontrivial H]
  (P : Measure Ω) [IsProbabilityMeasure P]
  (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
  (hcore : ∀h∈S,HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
  (p : ℝ≥0∞) [Fact (1≤p)] (hp : p≠⊤)

theorem gaussian_closed_derivative_frechet_norm {N : ℕ} (f : GaussianJet N) (e : Fin N → H)
    (he : Orthonormal ℝ e)
    (D : ∀k:ℕ,Lp (positiveMalliavinTensorPower H k) p P →ₗ.[ℝ]
      Lp (positiveMalliavinTensorPower H (k+1)) p P)
    (hD : ∀k (a : VectorCylinderExpr H (positiveMalliavinTensorPower H k)),
      (a.valueLp P W S hS hcore p hp,a.differentiate.valueLp P W S hS hcore p hp)∈(D k).graph)
    (k : ℕ) :
    (fun w => ‖(iteratedCylinderExpr H (f.toCylinder e) k).valueLp P W S hS hcore p hp w‖)=ᵐ[P]
      (fun w => Real.sqrt (∑a : Fin (k+1) → Fin N,
        ‖iteratedFDeriv ℝ (k+1) f.f (fun i => W (e i) w) (fun i => Pi.single (a i) 1)‖^2)) := by
  have hh := gaussian_scalar_higher_core_norm H P W S hS hcore p hp f e he D hD k
  simpa only [gaussianArrayNorm,gaussian_partial_frechet,Real.norm_eq_abs,sq_abs] using hh

theorem gaussian_closed_derivative_uniform_bound {N : ℕ} (f : GaussianJet N) (e : Fin N → H)
    (he : Orthonormal ℝ e)
    (D : ∀k:ℕ,Lp (positiveMalliavinTensorPower H k) p P →ₗ.[ℝ]
      Lp (positiveMalliavinTensorPower H (k+1)) p P)
    (hD : ∀k (a : VectorCylinderExpr H (positiveMalliavinTensorPower H k)),
      (a.valueLp P W S hS hcore p hp,a.differentiate.valueLp P W S hS hcore p hp)∈(D k).graph)
    (k : ℕ) (C : ℝ) (hC : 0≤C)
    (hb : ∀x,Real.sqrt (∑a : Fin (k+1) → Fin N,
      ‖iteratedFDeriv ℝ (k+1) f.f x (fun i => Pi.single (a i) 1)‖^2)≤C) :
    ‖(iteratedCylinderExpr H (f.toCylinder e) k).valueLp P W S hS hcore p hp‖≤C := by
  have hraw : ∀ᵐw ∂P,‖(iteratedCylinderExpr H (f.toCylinder e) k).valueLp P W S hS hcore p hp w‖≤C := by
    filter_upwards [gaussian_closed_derivative_frechet_norm H P W S hS hcore p hp f e he D hD k] with w hw
    rw [hw]
    exact hb _
  simpa [measureUnivNNReal] using Lp.norm_le_of_ae_bound hC hraw
end Asakura.Chapter12
#print axioms Asakura.Chapter12.gaussian_closed_derivative_uniform_bound

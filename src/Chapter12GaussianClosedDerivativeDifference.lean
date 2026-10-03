import Chapter12GaussianClosedDerivativeBound

open MeasureTheory ProbabilityTheory Set ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000

variable {Ω : Type*} [MeasurableSpace Ω] (H : RealHilbertSpaceData) [Nontrivial H]
  (P : Measure Ω) [IsProbabilityMeasure P]
  (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
  (hcore : ∀h∈S,HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
  (p : ℝ≥0∞) [Fact (1≤p)] (hp : p≠⊤)

theorem gaussian_closed_derivative_difference {N : ℕ} (f g : GaussianJet N) (e : Fin N → H)
    (he : Orthonormal ℝ e)
    (D : ∀k:ℕ,Lp (positiveMalliavinTensorPower H k) p P →ₗ.[ℝ]
      Lp (positiveMalliavinTensorPower H (k+1)) p P)
    (hD : ∀k (a : VectorCylinderExpr H (positiveMalliavinTensorPower H k)),
      (a.valueLp P W S hS hcore p hp,a.differentiate.valueLp P W S hS hcore p hp)∈(D k).graph)
    (k : ℕ) :
    (fun w => ‖((iteratedCylinderExpr H (f.toCylinder e) k).valueLp P W S hS hcore p hp-
      (iteratedCylinderExpr H (g.toCylinder e) k).valueLp P W S hS hcore p hp) w‖)=ᵐ[P]
      (fun w => Real.sqrt (∑a : Fin (k+1) → Fin N,
        ‖iteratedFDeriv ℝ (k+1) f.f (fun i => W (e i) w) (fun i => Pi.single (a i) 1)-
          iteratedFDeriv ℝ (k+1) g.f (fun i => W (e i) w) (fun i => Pi.single (a i) 1)‖^2)) := by
  rw [gaussian_scalar_higher_core H P W S hS hcore p hp f e D hD k,
    gaussian_scalar_higher_core H P W S hS hcore p hp g e D hD k]
  filter_upwards [Lp.coeFn_sub (gaussianTensorCore H P W S hS hcore p hp (fun i => f.partial i) e k)
      (gaussianTensorCore H P W S hS hcore p hp (fun i => g.partial i) e k),
    gaussian_tensor_core_coe H P W S hS hcore p hp (fun i => f.partial i) e k,
    gaussian_tensor_core_coe H P W S hS hcore p hp (fun i => g.partial i) e k] with w hw hf hg
  rw [hw,Pi.sub_apply,hf,hg,←Finset.sum_sub_distrib]
  simp_rw [←sub_smul]
  rw [tensor_coordinate_sum_norm H e he k]
  simp only [gaussian_gradient_tensorjet,gaussian_partial_frechet,Real.norm_eq_abs,sq_abs]

theorem gaussian_closed_derivative_difference_Lp {N : ℕ} (f g : GaussianJet N) (e : Fin N → H)
    (he : Orthonormal ℝ e)
    (D : ∀k:ℕ,Lp (positiveMalliavinTensorPower H k) p P →ₗ.[ℝ]
      Lp (positiveMalliavinTensorPower H (k+1)) p P)
    (hD : ∀k (a : VectorCylinderExpr H (positiveMalliavinTensorPower H k)),
      (a.valueLp P W S hS hcore p hp,a.differentiate.valueLp P W S hS hcore p hp)∈(D k).graph)
    (k : ℕ) (R : Lp ℝ p P)
    (hb : ∀ᵐw ∂P,Real.sqrt (∑a : Fin (k+1) → Fin N,
      ‖iteratedFDeriv ℝ (k+1) f.f (fun i => W (e i) w) (fun i => Pi.single (a i) 1)-
        iteratedFDeriv ℝ (k+1) g.f (fun i => W (e i) w) (fun i => Pi.single (a i) 1)‖^2)≤‖R w‖) :
    ‖(iteratedCylinderExpr H (f.toCylinder e) k).valueLp P W S hS hcore p hp-
      (iteratedCylinderExpr H (g.toCylinder e) k).valueLp P W S hS hcore p hp‖≤‖R‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [gaussian_closed_derivative_difference H P W S hS hcore p hp f g e he D hD k,hb] with w hw hb
  rw [hw]
  exact hb
end Asakura.Chapter12
#print axioms Asakura.Chapter12.gaussian_closed_derivative_difference_Lp

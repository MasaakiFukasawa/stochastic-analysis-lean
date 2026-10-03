import Chapter12FiniteVectorCoreRebasis
import Chapter12GaussianDerivativeFlatten

open MeasureTheory ProbabilityTheory Set ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

theorem gaussian_gradient_tensorjet {N : ℕ} (f : GaussianJet N) (k : ℕ)
    (b : Fin (k+1) → Fin N) :
    gaussianTensorJet (fun i => f.partial i) k b=f.iteratedPartial (List.ofFn b) := by
  rw [gaussianTensorJet_explicit,List.ofFn_succ_last,GaussianJet.iteratedPartial_append]
  rfl

theorem first_gradient_iterated_expression (H : RealHilbertSpaceData) (c : SmoothCylinder H) (k : ℕ) :
    iteratedVectorCylinderExpr H (cylinderFirstGradientExpr c) k=iteratedCylinderExpr H c k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [iteratedVectorCylinderExpr,iteratedCylinderExpr,ih]

variable {Ω : Type*} [MeasurableSpace Ω] (H : RealHilbertSpaceData) [Nontrivial H]
  (P : Measure Ω) [IsProbabilityMeasure P]
  (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
  (hcore : ∀ h∈S,HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
  (p : ℝ≥0∞) [Fact (1≤p)] (hp : p≠⊤)

theorem gaussian_scalar_higher_core {N : ℕ} (f : GaussianJet N) (e : Fin N → H)
    (D : ∀ k : ℕ,Lp (positiveMalliavinTensorPower H k) p P →ₗ.[ℝ]
      Lp (positiveMalliavinTensorPower H (k+1)) p P)
    (hD : ∀ k (a : VectorCylinderExpr H (positiveMalliavinTensorPower H k)),
      (a.valueLp P W S hS hcore p hp,a.differentiate.valueLp P W S hS hcore p hp)∈(D k).graph)
    (k : ℕ) :
    (iteratedCylinderExpr H (f.toCylinder e) k).valueLp P W S hS hcore p hp=
      gaussianTensorCore H P W S hS hcore p hp (fun i => f.partial i) e k := by
  have h0 : (cylinderFirstGradientExpr (f.toCylinder e)).valueLp P W S hS hcore p hp=
      gaussianTensorCore H P W S hS hcore p hp (fun i => f.partial i) e 0 := by
    change (∑ i : Fin N,vectorCylinderValue P W S hS hcore ((f.partial i).toCylinder e) (e i) p hp)=
      ∑ b : Fin 1 → Fin N,vectorCylinderValue P W S hS hcore ((f.partial (b 0)).toCylinder e) (e (b 0)) p hp
    exact (Equiv.sum_comp (Equiv.funUnique (Fin 1) (Fin N))
      (fun i => vectorCylinderValue P W S hS hcore ((f.partial i).toCylinder e) (e i) p hp)).symm
  simpa only [first_gradient_iterated_expression] using
    vector_rebasis_all_derivatives H P W S hS hcore (cylinderFirstGradientExpr (f.toCylinder e))
      p hp D hD (fun i => f.partial i) e h0 k

theorem gaussian_scalar_higher_core_norm {N : ℕ} (f : GaussianJet N) (e : Fin N → H)
    (he : Orthonormal ℝ e)
    (D : ∀ k : ℕ,Lp (positiveMalliavinTensorPower H k) p P →ₗ.[ℝ]
      Lp (positiveMalliavinTensorPower H (k+1)) p P)
    (hD : ∀ k (a : VectorCylinderExpr H (positiveMalliavinTensorPower H k)),
      (a.valueLp P W S hS hcore p hp,a.differentiate.valueLp P W S hS hcore p hp)∈(D k).graph)
    (k : ℕ) :
    (fun w => ‖(iteratedCylinderExpr H (f.toCylinder e) k).valueLp P W S hS hcore p hp w‖)=ᵐ[P]
      (fun w => gaussianArrayNorm (fun b : Fin (k+1) → Fin N => f.iteratedPartial (List.ofFn b))
        (fun i => W (e i) w)) := by
  rw [gaussian_scalar_higher_core H P W S hS hcore p hp f e D hD k]
  have heq : gaussianTensorJet (fun i => f.partial i) k=(fun b => f.iteratedPartial (List.ofFn b)) :=
    funext (gaussian_gradient_tensorjet f k)
  simpa only [heq] using
    gaussian_tensor_core_norm H P W S hS hcore p hp (fun i => f.partial i) e he k

end Asakura.Chapter12

import Chapter12GaussianPathTensor

open MeasureTheory ProbabilityTheory Set ENNReal
open scoped ContDiff
namespace Asakura.Chapter12
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

theorem gaussian_path_tensor_core {Ω : Type*} [MeasurableSpace Ω]
    (H : RealHilbertSpaceData) [Nontrivial H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀u∈S,HasLaw (W u : Ω → ℝ) (gaussianReal 0 ⟨‖u‖^2,sq_nonneg _⟩) P)
    (p : ℝ≥0∞) [Fact (1≤p)] (hp : p≠⊤)
    {N : ℕ} {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (e : Fin N → H) (X : (Fin N → ℝ) → C(K,ℝ)) (hX : ContDiff ℝ ∞ X)
    (t : K) (f : GaussianJet N) (hf : f.f=fun z => X z t)
    (D : ∀k:ℕ,Lp (positiveMalliavinTensorPower H k) p P →ₗ.[ℝ]
      Lp (positiveMalliavinTensorPower H (k+1)) p P)
    (hD : ∀k (a : VectorCylinderExpr H (positiveMalliavinTensorPower H k)),
      (a.valueLp P W S hS hcore p hp,a.differentiate.valueLp P W S hS hcore p hp)∈(D k).graph)
    (k : ℕ) :
    ((iteratedCylinderExpr H (f.toCylinder e) k).valueLp P W S hS hcore p hp : Ω → positiveMalliavinTensorPower H k)=ᵐ[P]
      (fun w => gaussianPathTensor H e X k (fun i => W (e i) w) t) := by
  rw [gaussian_scalar_higher_core H P W S hS hcore p hp f e D hD k]
  filter_upwards [gaussian_tensor_core_coe H P W S hS hcore p hp (fun i => f.partial i) e k] with w hw
  rw [hw,gaussianPathTensor_apply]
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  rw [gaussian_gradient_tensorjet,gaussian_partial_frechet,hf]
  exact path_derivative_evaluation X hX (k+1) _ _ t
end Asakura.Chapter12
#print axioms Asakura.Chapter12.gaussian_path_tensor_core

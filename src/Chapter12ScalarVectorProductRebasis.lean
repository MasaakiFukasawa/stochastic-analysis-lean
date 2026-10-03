import Chapter12VectorCylinderScalarProduct

open MeasureTheory ProbabilityTheory Set ENNReal
namespace Asakura.Chapter12
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

theorem scalar_vector_product_rebasis {Ω:Type*} [MeasurableSpace Ω]
    (H:RealHilbertSpaceData) [Nontrivial H] (P:Measure Ω) [IsProbabilityMeasure P]
    (W:H →ₗᵢ[ℝ] Lp ℝ 2 P) (S:Set H) (hS:Dense S)
    (hcore:∀u∈S,HasLaw (W u : Ω → ℝ) (gaussianReal 0 ⟨‖u‖^2,sq_nonneg _⟩) P)
    (p:ℝ≥0∞) [Fact (1≤p)] (hp:p≠⊤)
    (f:SmoothCylinder H) (c:VectorCylinderExpr H H)
    {N:ℕ} (a:GaussianJet N) (u:Fin N → GaussianJet N) (e:Fin N → H)
    (hf:f.value P W=ᵐ[P] (a.toCylinder e).value P W)
    (hc:c.valueLp P W S hS hcore p hp=gaussianTensorCore H P W S hS hcore p hp u e 0) :
    (c.scalarProduct f).valueLp P W S hS hcore p hp=
      gaussianTensorCore H P W S hS hcore p hp (fun i => a.mul (u i)) e 0 := by
  apply Lp.ext
  filter_upwards [(c.scalarProduct f).valueLp_coe H P W S hS hcore p hp,hf,
    vector_rebased_raw_value H P W S hS hcore c u e p hp hc,
    gaussian_tensor_core_zero_coe H P W S hS hcore (fun i => a.mul (u i)) e p hp] with w hw hf hc hz
  rw [hw,VectorCylinderExpr.scalarProduct_rawValue,hf,hc,hz,gaussian_vector_scalar_product_function]
  rfl
end Asakura.Chapter12
#print axioms Asakura.Chapter12.scalar_vector_product_rebasis

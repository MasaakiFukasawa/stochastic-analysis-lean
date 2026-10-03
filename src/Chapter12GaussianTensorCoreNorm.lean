import Chapter12GaussianTensorCore

open MeasureTheory ProbabilityTheory Set ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

variable {Ω : Type*} [MeasurableSpace Ω] (H : RealHilbertSpaceData) [Nontrivial H]
  (P : Measure Ω) [IsProbabilityMeasure P]
  (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
  (hcore : ∀ h∈S,HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
  (p : ℝ≥0∞) [Fact (1≤p)] (hp : p≠⊤)

theorem vector_cylinder_value_coe {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (c : SmoothCylinder H) (v : E) :
    (vectorCylinderValue P W S hS hcore c v p hp : Ω → E)=ᵐ[P]
      (fun w => c.value P W w • v) := by
  have hc := (c.value_memLp P W S hS hcore p hp).coeFn_toLp
  have hl := ((ContinuousLinearMap.id ℝ ℝ).smulRight v).coeFn_compLp (c.valueLp P W S hS hcore p hp)
  filter_upwards [hc,hl] with w hw hlw
  change c.valueLp P W S hS hcore p hp w=c.value P W w at hw
  change ((ContinuousLinearMap.id ℝ ℝ).smulRight v).compLp (c.valueLp P W S hS hcore p hp) w=_
  rw [hlw,ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.id_apply,hw]

theorem gaussian_tensor_core_coe {N : ℕ} (u : Fin N → GaussianJet N) (e : Fin N → H) (k : ℕ) :
    (gaussianTensorCore H P W S hS hcore p hp u e k : Ω → positiveMalliavinTensorPower H k)=ᵐ[P]
      (fun w => ∑ b,(gaussianTensorJet u k b).f (fun i => W (e i) w) • tensorCoordinateFrame H e k b) := by
  have hs := Lp.coeFn_fun_finsetSum Finset.univ (fun b : Fin (k+1) → Fin N =>
    vectorCylinderValue P W S hS hcore ((gaussianTensorJet u k b).toCylinder e)
      (tensorCoordinateFrame H e k b) p hp)
  have ht := ae_all_iff.mpr (fun b : Fin (k+1) → Fin N =>
    vector_cylinder_value_coe H P W S hS hcore p hp ((gaussianTensorJet u k b).toCylinder e)
      (tensorCoordinateFrame H e k b))
  filter_upwards [hs,ht] with w hw ht
  change (∑ b,vectorCylinderValue P W S hS hcore ((gaussianTensorJet u k b).toCylinder e)
    (tensorCoordinateFrame H e k b) p hp) w=_
  rw [hw]
  apply Finset.sum_congr rfl
  intro b _
  exact ht b

/-- Actual Lp representatives of the iterated core derivative have the
finite Hilbert--Schmidt coordinate norm almost everywhere. -/
theorem gaussian_tensor_core_norm {N : ℕ} (u : Fin N → GaussianJet N) (e : Fin N → H)
    (he : Orthonormal ℝ e) (k : ℕ) :
    (fun w => ‖gaussianTensorCore H P W S hS hcore p hp u e k w‖)=ᵐ[P]
      (fun w => gaussianArrayNorm (gaussianTensorJet u k) (fun i => W (e i) w)) := by
  filter_upwards [gaussian_tensor_core_coe H P W S hS hcore p hp u e k] with w hw
  rw [hw,tensor_coordinate_sum_norm H e he k]
  rfl

end Asakura.Chapter12

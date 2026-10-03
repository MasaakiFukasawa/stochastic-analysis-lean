import Chapter12GaussianPathTensorCore
import Chapter12ContinuousPathAEEquality
import Chapter12CylinderValueEquality
import Chapter12ScalarJetOperatorsFromCore

open MeasureTheory ProbabilityTheory Set ENNReal TopologicalSpace
open scoped ContDiff
namespace Asakura.Chapter12
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

theorem gaussian_path_tensor_rebasis {Ω : Type*} [MeasurableSpace Ω]
    (H : RealHilbertSpaceData) [Nontrivial H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀u∈S,HasLaw (W u : Ω → ℝ) (gaussianReal 0 ⟨‖u‖^2,sq_nonneg _⟩) P)
    (hdense : DenseRange (fun c : SmoothCylinder H => c.valueLp P W S hS hcore 2 (by simp)))
    {N M : ℕ} {K : Type*} [TopologicalSpace K] [CompactSpace K] [SeparableSpace K] [Nonempty K]
    (e : Fin N → H) (f : Fin M → H)
    (X : (Fin N → ℝ) → C(K,ℝ)) (Y : (Fin M → ℝ) → C(K,ℝ))
    (hX : ContDiff ℝ ∞ X) (hY : ContDiff ℝ ∞ Y)
    (hXjet : ∀t,∃a : GaussianJet N,a.f=fun z => X z t)
    (hYjet : ∀t,∃a : GaussianJet M,a.f=fun z => Y z t)
    (hXY : (fun w => X (fun i => W (e i) w))=ᵐ[P] (fun w => Y (fun i => W (f i) w)))
    (k : ℕ) :
    (fun w => gaussianPathTensor H e X k (fun i => W (e i) w))=ᵐ[P]
      (fun w => gaussianPathTensor H f Y k (fun i => W (f i) w)) := by
  apply continuous_path_ae_equality P
  intro t
  obtain ⟨a,ha⟩ := hXjet t
  obtain ⟨b,hb⟩ := hYjet t
  have hv : (a.toCylinder e).value P W=ᵐ[P] (b.toCylinder f).value P W := by
    filter_upwards [hXY] with w hw
    change a.f (fun i => W (e i) w)=b.f (fun i => W (f i) w)
    rw [ha,hb]
    exact congrArg (fun q : C(K,ℝ) => q t) hw
  have h0 := cylinder_value_equality H P W S hS hcore 2 (by simp) _ _ hv
  have hj := scalar_jet_core_unique H P W S hS hcore 2 2 (by simp) (by simp) hdense _ _ h0 (k+1)
  change (iteratedCylinderExpr H (a.toCylinder e) k).valueLp P W S hS hcore 2 (by simp)=
    (iteratedCylinderExpr H (b.toCylinder f) k).valueLp P W S hS hcore 2 (by simp) at hj
  obtain ⟨D,hclosed,hD⟩ := higher_vector_core_operators H P W S hS hcore 2 2 (by simp) (by simp) hdense
  have hca := gaussian_path_tensor_core H P W S hS hcore 2 (by simp) e X hX t a ha D hD k
  have hcb := gaussian_path_tensor_core H P W S hS hcore 2 (by simp) f Y hY t b hb D hD k
  rw [hj] at hca
  exact hca.symm.trans hcb
end Asakura.Chapter12
#print axioms Asakura.Chapter12.gaussian_path_tensor_rebasis

import Chapter12CompositionPolynomialStability
import Chapter12RebasedAllJetNorms
import Chapter12TwoCylinderCommonFrame
import Chapter12GaussianJetSmoothComposition
import Chapter12VectorJetSize
import Chapter12VectorCylinderSquare
import Chapter12RebasedVectorJetNorms
import Chapter12HilbertNormSquareGrowth

open MeasureTheory ProbabilityTheory Set ENNReal
open scoped ContDiff
namespace Asakura.Chapter12
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false

theorem vector_square_value_estimate {Ω : Type*} [MeasurableSpace Ω]
    (H : RealHilbertSpaceData) [Nontrivial H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀u∈S,HasLaw (W u : Ω → ℝ) (gaussianReal 0 ⟨‖u‖^2,sq_nonneg _⟩) P)
    (p q r s : ℝ≥0∞) [Fact (1≤p)] [Fact (1≤q)] [Fact (1≤r)] [Fact (1≤s)]
    [HolderConjugate p q] [HolderConjugate r s]
    (hp : p≠⊤) (hq : q≠⊤) (hr : r≠⊤) (hs : s≠⊤)
    (hdq : DenseRange (fun c : SmoothCylinder H => c.valueLp P W S hS hcore q hq))
    (hds : DenseRange (fun c : SmoothCylinder H => c.valueLp P W S hS hcore s hs))
    (K : ℝ) (hK0 : 0≤K) (a : ℕ)
    (hKB : ∀j≤0+1,∀x,‖iteratedFDeriv ℝ j (fun y:H => ‖y‖^2) x‖≤K*(1+‖x‖)^a)
    (c d : VectorCylinderExpr H H) (f g : SmoothCylinder H)
    (hf : f.value P W=ᵐ[P] (fun w => ‖c.rawValue P W w‖^2))
    (hg : g.value P W=ᵐ[P] (fun w => ‖d.rawValue P W w‖^2)) : ∀ᵐw ∂P,
      ‖(cylinderJetCoordinate H P W S hS hcore p hp f 0-
        cylinderJetCoordinate H P W S hS hcore p hp g 0) w‖≤
        K*(1+vectorJetSize H P W S hS hcore r hr c 0 w+
          vectorJetSize H P W S hS hcore r hr d 0 w)^a*
          vectorJetDistance H P W S hS hcore r hr c d 0 w := by
  obtain ⟨N,e,u,he,hu⟩ := vector_expr_family_rebasis H P W S hS hcore
    (fun i:Fin 2 => if i=0 then c else d)
  let U := u 0
  let V := u 1
  have hc0 : c.valueLp P W S hS hcore r hr=gaussianTensorCore H P W S hS hcore r hr U e 0 := by simpa [U] using hu 0 r hr
  have hd0 : d.valueLp P W S hS hcore r hr=gaussianTensorCore H P W S hS hcore r hr V e 0 := by simpa [V] using hu 1 r hr
  have hc := vector_rebased_raw_value H P W S hS hcore c U e r hr hc0
  have hd := vector_rebased_raw_value H P W S hS hcore d V e r hr hd0
  have hcf : f.value P W=ᵐ[P] ((gaussianVectorNormSquare U).toCylinder e).value P W := by
    filter_upwards [hf,hc] with w hw hz
    rw [hw,hz]
    change _=(gaussianVectorNormSquare U).f (fun i => W (e i) w)
    rw [gaussianVectorNormSquare_value U e he,Function.comp_apply]
  have hdg : g.value P W=ᵐ[P] ((gaussianVectorNormSquare V).toCylinder e).value P W := by
    filter_upwards [hg,hd] with w hw hz
    rw [hw,hz]
    change _=(gaussianVectorNormSquare V).f (fun i => W (e i) w)
    rw [gaussianVectorNormSquare_value V e he,Function.comp_apply]
  have ho := rebased_all_jet_norms H P W S hS hcore p q hp hq hdq f g
    (gaussianVectorNormSquare U) (gaussianVectorNormSquare V) e he hcf hdg 0
  have hfn j := rebased_vector_jet_norm H P W S hS hcore r s hr hs hds c U e he hc0 j
  have hgn j := rebased_vector_jet_norm H P W S hS hcore r s hr hs hds d V e he hd0 j
  have hdf j := rebased_vector_jet_difference_norm H P W S hS hcore r s hr hs hds c d U V e he hc0 hd0 j
  filter_upwards [ho,ae_all_iff.mpr hfn,ae_all_iff.mpr hgn,ae_all_iff.mpr hdf] with w how hfw hgw hdw
  rw [how]
  let z := fun i => W (e i) w
  let R := 1+vectorJetSize H P W S hS hcore r hr c 0 w+vectorJetSize H P W S hS hcore r hr d 0 w
  let δ := vectorJetDistance H P W S hS hcore r hr c d 0 w
  have hcj j (hj : j≤0) : ‖(iteratedVectorCylinderExpr H c j).valueLp P W S hS hcore r hr w‖≤
      vectorJetSize H P W S hS hcore r hr c 0 w :=
    finite_sum_norm_member (fun i:Fin (0+1) => positiveMalliavinTensorPower H i.val)
      (fun i => (iteratedVectorCylinderExpr H c i.val).valueLp P W S hS hcore r hr w) ⟨j,by omega⟩
  have hdj j (hj : j≤0) : ‖(iteratedVectorCylinderExpr H d j).valueLp P W S hS hcore r hr w‖≤
      vectorJetSize H P W S hS hcore r hr d 0 w :=
    finite_sum_norm_member (fun i:Fin (0+1) => positiveMalliavinTensorPower H i.val)
      (fun i => (iteratedVectorCylinderExpr H d i.val).valueLp P W S hS hcore r hr w) ⟨j,by omega⟩
  have hδj j (hj : j≤0) : ‖((iteratedVectorCylinderExpr H c j).valueLp P W S hS hcore r hr-
      (iteratedVectorCylinderExpr H d j).valueLp P W S hS hcore r hr) w‖≤δ :=
    finite_sum_norm_member (fun i:Fin (0+1) => positiveMalliavinTensorPower H i.val)
      (fun i => ((iteratedVectorCylinderExpr H c i.val).valueLp P W S hS hcore r hr-
        (iteratedVectorCylinderExpr H d i.val).valueLp P W S hS hcore r hr) w) ⟨j,by omega⟩
  have hcn : 0≤vectorJetSize H P W S hS hcore r hr c 0 w := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hdn : 0≤vectorJetSize H P W S hS hcore r hr d 0 w := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hδ : 0≤δ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hf0 := hfw 0
  have hg0 := hgw 0
  have hdiff0 := hdw 0
  simp only [iteratedFDeriv_zero_apply,Finset.sum_const,Finset.card_univ,Fintype.card_fun,
    Fintype.card_fin,pow_zero,one_smul,Real.sqrt_sq (norm_nonneg _)] at hf0 hg0 hdiff0
  rw [gaussianVectorNormSquare_value U e he,gaussianVectorNormSquare_value V e he]
  have hm := polynomial_derivative_difference (fun y:H => ‖y‖^2) (contDiff_norm_sq ℝ) 0 a K hK0
    (hKB 1 le_rfl) (gaussianVectorFunction U e z) (gaussianVectorFunction V e z)
  simp only [iteratedFDeriv_zero_eq_comp,Function.comp_apply,←map_sub,LinearIsometryEquiv.norm_map] at hm
  simp only [Function.comp_apply,iteratedFDeriv_zero_apply,
    Finset.sum_const,Finset.card_univ,Fintype.card_fun,Fintype.card_fin,pow_zero,
    one_smul,Real.sqrt_sq (norm_nonneg _)]
  apply hm.trans
  apply mul_le_mul
  · apply mul_le_mul_of_nonneg_left _ hK0
    apply pow_le_pow_left₀ (by positivity)
    rw [←hf0,←hg0]
    exact add_le_add (add_le_add_right (hcj 0 le_rfl) 1) (hdj 0 le_rfl)
  · rw [←hdiff0]
    exact hδj 0 le_rfl
  · exact norm_nonneg _
  · positivity
end Asakura.Chapter12
#print axioms Asakura.Chapter12.vector_square_value_estimate

import Chapter12MixedCommonFrame
import Chapter12ScalarVectorProductRebasis
import Chapter12ScalarVectorValueStability
import Chapter12RebasedVectorJetNorms
import Chapter12RebasedAllJetNorms
import Chapter12VectorJetSize
import Chapter12FinitePrefixMember

open MeasureTheory ProbabilityTheory Set ENNReal
namespace Asakura.Chapter12
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

theorem scalar_vector_core_value_estimate {Ω:Type*} [MeasurableSpace Ω]
    (H:RealHilbertSpaceData) [Nontrivial H] (P:Measure Ω) [IsProbabilityMeasure P]
    (W:H →ₗᵢ[ℝ] Lp ℝ 2 P) (S:Set H) (hS:Dense S)
    (hcore:∀u∈S,HasLaw (W u : Ω → ℝ) (gaussianReal 0 ⟨‖u‖^2,sq_nonneg _⟩) P)
    (p q r s:ℝ≥0∞) [Fact (1≤p)] [Fact (1≤q)] [Fact (1≤r)] [Fact (1≤s)]
    [HolderConjugate p q] [HolderConjugate r s]
    (hp:p≠⊤) (hq:q≠⊤) (hr:r≠⊤) (hs:s≠⊤)
    (hdq:DenseRange (fun c:SmoothCylinder H => c.valueLp P W S hS hcore q hq))
    (hds:DenseRange (fun c:SmoothCylinder H => c.valueLp P W S hS hcore s hs))
    (K:ℝ) (hK:0≤K) (a:ℕ)
    (hB:∀j≤0+1,∀x:ℝ×H,‖iteratedFDeriv ℝ j (fun y:ℝ×H => y.1 • y.2) x‖≤K*(1+‖x‖)^a)
    (f g:SmoothCylinder H) (c d:VectorCylinderExpr H H) : ∀ᵐw ∂P,
    ‖((iteratedVectorCylinderExpr H (c.scalarProduct f) 0).valueLp P W S hS hcore p hp-
      (iteratedVectorCylinderExpr H (d.scalarProduct g) 0).valueLp P W S hS hcore p hp) w‖≤
    K*
      (1+cylinderJetSize H P W S hS hcore r hr f 0 w+cylinderJetSize H P W S hS hcore r hr g 0 w+
        vectorJetSize H P W S hS hcore r hr c 0 w+vectorJetSize H P W S hS hcore r hr d 0 w)^a*
      (cylinderJetDistance H P W S hS hcore r hr f g 0 w+vectorJetDistance H P W S hS hcore r hr c d 0 w) := by
  obtain ⟨N,e,A,B,U,V,he,hf,hg,hv⟩ := mixed_common_frame H P W S hS hcore f g c d
  have hcf := scalar_vector_product_rebasis H P W S hS hcore p hp f c A U e hf (hv p hp).1
  have hdg := scalar_vector_product_rebasis H P W S hS hcore p hp g d B V e hg (hv p hp).2
  have ho := rebased_vector_jet_difference_norm H P W S hS hcore p q hp hq hdq
    (c.scalarProduct f) (d.scalarProduct g) (fun i => A.mul (U i)) (fun i => B.mul (V i)) e he hcf hdg 0
  have hfn j := rebased_single_jet_norm H P W S hS hcore r s hr hs hds f A e he hf j
  have hgn j := rebased_single_jet_norm H P W S hS hcore r s hr hs hds g B e he hg j
  have hcn j := rebased_vector_jet_norm H P W S hS hcore r s hr hs hds c U e he (hv r hr).1 j
  have hdn j := rebased_vector_jet_norm H P W S hS hcore r s hr hs hds d V e he (hv r hr).2 j
  have hsd j := rebased_all_jet_norms H P W S hS hcore r s hr hs hds f g A B e he hf hg j
  have hvd j := rebased_vector_jet_difference_norm H P W S hS hcore r s hr hs hds c d U V e he (hv r hr).1 (hv r hr).2 j
  filter_upwards [ho,ae_all_iff.mpr hfn,ae_all_iff.mpr hgn,ae_all_iff.mpr hcn,ae_all_iff.mpr hdn,
    ae_all_iff.mpr hsd,ae_all_iff.mpr hvd] with w how hfω hgω hcω hdω hsω hvω
  rw [how,gaussian_vector_scalar_product_function,gaussian_vector_scalar_product_function]
  let z := fun i => W (e i) w
  let R := 1+cylinderJetSize H P W S hS hcore r hr f 0 w+cylinderJetSize H P W S hS hcore r hr g 0 w+
    vectorJetSize H P W S hS hcore r hr c 0 w+vectorJetSize H P W S hS hcore r hr d 0 w
  let δ := cylinderJetDistance H P W S hS hcore r hr f g 0 w+vectorJetDistance H P W S hS hcore r hr c d 0 w
  have hfn0 : 0≤cylinderJetSize H P W S hS hcore r hr f 0 w := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hgn0 : 0≤cylinderJetSize H P W S hS hcore r hr g 0 w := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hcn0 : 0≤vectorJetSize H P W S hS hcore r hr c 0 w := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hdn0 : 0≤vectorJetSize H P W S hS hcore r hr d 0 w := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hδ : 0≤δ := add_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  have hfmem j (hj:j≤0) := finite_prefix_member_le
    (fun i => ‖cylinderJetCoordinate H P W S hS hcore r hr f i w‖) (fun _ => norm_nonneg _) hj
  have hgmem j (hj:j≤0) := finite_prefix_member_le
    (fun i => ‖cylinderJetCoordinate H P W S hS hcore r hr g i w‖) (fun _ => norm_nonneg _) hj
  have hcmem j (hj:j≤0) := finite_prefix_member_le
    (fun i => ‖(iteratedVectorCylinderExpr H c i).valueLp P W S hS hcore r hr w‖) (fun _ => norm_nonneg _) hj
  have hdmem j (hj:j≤0) := finite_prefix_member_le
    (fun i => ‖(iteratedVectorCylinderExpr H d i).valueLp P W S hS hcore r hr w‖) (fun _ => norm_nonneg _) hj
  have hsmem j (hj:j≤0) := finite_prefix_member_le
    (fun i => ‖(cylinderJetCoordinate H P W S hS hcore r hr f i-cylinderJetCoordinate H P W S hS hcore r hr g i) w‖)
    (fun _ => norm_nonneg _) hj
  have hvmem j (hj:j≤0) := finite_prefix_member_le
    (fun i => ‖((iteratedVectorCylinderExpr H c i).valueLp P W S hS hcore r hr-
      (iteratedVectorCylinderExpr H d i).valueLp P W S hS hcore r hr) w‖) (fun _ => norm_nonneg _) hj
  have hf0 := hfω 0
  have hg0 := hgω 0
  have hc0 := hcω 0
  have hd0 := hdω 0
  have hs0 := hsω 0
  have hv0 := hvω 0
  simp only [iteratedFDeriv_zero_apply,Finset.sum_const,Finset.card_univ,Fintype.card_fun,
    Fintype.card_fin,pow_zero,one_smul,Real.sqrt_sq (norm_nonneg _)] at hf0 hg0 hc0 hd0 hs0 hv0
  simp only [iteratedFDeriv_zero_apply,Finset.sum_const,Finset.card_univ,Fintype.card_fun,
    Fintype.card_fin,pow_zero,one_smul,Real.sqrt_sq (norm_nonneg _)]
  apply scalar_vector_value_stability (A.f z) (B.f z) (gaussianVectorFunction U e z)
    (gaussianVectorFunction V e z) K R δ a hK (by dsimp only [R];linarith) hδ (hB 1 le_rfl)
  · rw [←hf0,←hg0,←hc0,←hd0]
    exact add_le_add (add_le_add (add_le_add (add_le_add_right (hfmem 0 (Nat.zero_le _)) 1)
      (hgmem 0 (Nat.zero_le _))) (hcmem 0 (Nat.zero_le _))) (hdmem 0 (Nat.zero_le _))
  · rw [←hs0,←hv0]
    exact add_le_add (hsmem 0 (Nat.zero_le _)) (hvmem 0 (Nat.zero_le _))
end Asakura.Chapter12
#print axioms Asakura.Chapter12.scalar_vector_core_value_estimate

import Chapter12CompositionPolynomialStability
import Chapter12RebasedAllJetNorms
import Chapter12TwoCylinderCommonFrame
import Chapter12GaussianJetSmoothComposition
import Chapter12CylinderJetSize

open MeasureTheory ProbabilityTheory Set ENNReal
open scoped ContDiff
namespace Asakura.Chapter12
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false

theorem cylinder_value_composition_explicit_estimate {Ω : Type*} [MeasurableSpace Ω]
    (H : RealHilbertSpaceData) [Nontrivial H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀u∈S,HasLaw (W u : Ω → ℝ) (gaussianReal 0 ⟨‖u‖^2,sq_nonneg _⟩) P)
    (p q r s : ℝ≥0∞) [Fact (1≤p)] [Fact (1≤q)] [Fact (1≤r)] [Fact (1≤s)]
    [HolderConjugate p q] [HolderConjugate r s]
    (hp : p≠⊤) (hq : q≠⊤) (hr : r≠⊤) (hs : s≠⊤)
    (hdq : DenseRange (fun c : SmoothCylinder H => c.valueLp P W S hS hcore q hq))
    (hds : DenseRange (fun c : SmoothCylinder H => c.valueLp P W S hS hcore s hs))
    (b : ℝ → ℝ) (hb : ContDiff ℝ ∞ b)
    (hB : ∀j:ℕ,∃C:ℝ,0≤C ∧ ∃a:ℕ,∀x,‖iteratedFDeriv ℝ j b x‖≤C*(1+‖x‖)^a)
    (K : ℝ) (hK0 : 0≤K) (a : ℕ)
    (hKB : ∀j≤1,∀x,‖iteratedFDeriv ℝ j b x‖≤K*(1+‖x‖)^a)
    (c d : SmoothCylinder H) : ∀ᵐw ∂P,
      ‖(cylinderJetCoordinate H P W S hS hcore p hp (composeSmoothCylinder c b hb hB) 0-
        cylinderJetCoordinate H P W S hS hcore p hp (composeSmoothCylinder d b hb hB) 0) w‖≤
        K*(1+cylinderJetSize H P W S hS hcore r hr c 0 w+
          cylinderJetSize H P W S hS hcore r hr d 0 w)^a*
          cylinderJetDistance H P W S hS hcore r hr c d 0 w := by
  obtain ⟨N,e,f,g,he,hc,hd⟩ := two_cylinder_common_frame P W c d
  have hcf : (composeSmoothCylinder c b hb hB).value P W=ᵐ[P]
      ((f.compSmooth b hb hB).toCylinder e).value P W := by
    exact hc.fun_comp b
  have hdg : (composeSmoothCylinder d b hb hB).value P W=ᵐ[P]
      ((g.compSmooth b hb hB).toCylinder e).value P W := by
    exact hd.fun_comp b
  have ho := rebased_all_jet_norms H P W S hS hcore p q hp hq hdq _ _
    (f.compSmooth b hb hB) (g.compSmooth b hb hB) e he hcf hdg 0
  have hfn j := rebased_single_jet_norm H P W S hS hcore r s hr hs hds c f e he hc j
  have hgn j := rebased_single_jet_norm H P W S hS hcore r s hr hs hds d g e he hd j
  have hdf j := rebased_all_jet_norms H P W S hS hcore r s hr hs hds c d f g e he hc hd j
  filter_upwards [ho,ae_all_iff.mpr hfn,ae_all_iff.mpr hgn,ae_all_iff.mpr hdf] with w how hfw hgw hdw
  rw [how]
  let z := fun i => W (e i) w
  let R := 1+cylinderJetSize H P W S hS hcore r hr c 0 w+cylinderJetSize H P W S hS hcore r hr d 0 w
  let δ := cylinderJetDistance H P W S hS hcore r hr c d 0 w
  have hcj j (hj : j≤0) : ‖cylinderJetCoordinate H P W S hS hcore r hr c j w‖≤
      cylinderJetSize H P W S hS hcore r hr c 0 w :=
    finite_sum_norm_member (fun i:Fin (0+1) => malliavinTensorOrder H i.val)
      (fun i => cylinderJetCoordinate H P W S hS hcore r hr c i.val w) ⟨j,by omega⟩
  have hdj j (hj : j≤0) : ‖cylinderJetCoordinate H P W S hS hcore r hr d j w‖≤
      cylinderJetSize H P W S hS hcore r hr d 0 w :=
    finite_sum_norm_member (fun i:Fin (0+1) => malliavinTensorOrder H i.val)
      (fun i => cylinderJetCoordinate H P W S hS hcore r hr d i.val w) ⟨j,by omega⟩
  have hδj j (hj : j≤0) : ‖(cylinderJetCoordinate H P W S hS hcore r hr c j-
      cylinderJetCoordinate H P W S hS hcore r hr d j) w‖≤δ :=
    finite_sum_norm_member (fun i:Fin (0+1) => malliavinTensorOrder H i.val)
      (fun i => (cylinderJetCoordinate H P W S hS hcore r hr c i.val-
        cylinderJetCoordinate H P W S hS hcore r hr d i.val) w) ⟨j,by omega⟩
  have hcn : 0≤cylinderJetSize H P W S hS hcore r hr c 0 w := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hdn : 0≤cylinderJetSize H P W S hS hcore r hr d 0 w := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hδ : 0≤δ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hf0 := hfw 0
  have hg0 := hgw 0
  have hd0 := hdw 0
  simp only [iteratedFDeriv_zero_apply,Finset.sum_const,Finset.card_univ,Fintype.card_fun,
    Fintype.card_fin,pow_zero,one_smul,Real.sqrt_sq (norm_nonneg _)] at hf0 hg0 hd0
  have hm := polynomial_derivative_difference b hb 0 a K hK0 (hKB 1 le_rfl) (f.f z) (g.f z)
  simp only [iteratedFDeriv_zero_eq_comp,Function.comp_apply,←map_sub,LinearIsometryEquiv.norm_map] at hm
  simp only [GaussianJet.compSmooth,Function.comp_apply,iteratedFDeriv_zero_apply,
    Finset.sum_const,Finset.card_univ,Fintype.card_fun,Fintype.card_fin,pow_zero,
    one_smul,Real.sqrt_sq (norm_nonneg _)]
  apply hm.trans
  apply mul_le_mul
  · apply mul_le_mul_of_nonneg_left _ hK0
    apply pow_le_pow_left₀ (by positivity)
    rw [←hf0,←hg0]
    exact add_le_add (add_le_add_right (hcj 0 le_rfl) 1) (hdj 0 le_rfl)
  · rw [←hd0]
    exact hδj 0 le_rfl
  · exact norm_nonneg _
  · positivity
end Asakura.Chapter12
#print axioms Asakura.Chapter12.cylinder_value_composition_explicit_estimate

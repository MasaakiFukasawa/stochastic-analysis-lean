import Chapter12AllSobolevReciprocalSquare
import Chapter12LpNormPowerMember

open MeasureTheory ProbabilityTheory Set ENNReal
namespace Asakura.Chapter12
set_option maxHeartbeats 3400000
set_option backward.isDefEq.respectTransparency false

theorem all_sobolev_reciprocal {Ω:Type*} [MeasurableSpace Ω]
    (H:RealHilbertSpaceData) [Nontrivial H] (P:Measure Ω) [IsProbabilityMeasure P]
    (W:H →ₗᵢ[ℝ] Lp ℝ 2 P) (S:Set H) (hS:Dense S)
    (hcore:∀u∈S,HasLaw (W u:Ω → ℝ) (gaussianReal 0 ⟨‖u‖^2,sq_nonneg _⟩) P)
    (hdense:∀(q:ℝ≥0∞) [Fact (1≤q)] (hq:q≠⊤),
      DenseRange (fun c:SmoothCylinder H => c.valueLp P W S hS hcore q hq))
    (D:Lp ℝ 2 P →ₗ.[ℝ] Lp H 2 P) (hD:D.IsClosed)
    (hg:(D.graph:Set _)=closure (range (cylinderPair P W S hS hcore 2 (by simp))))
    (G:Ω → ℝ) (hG:HasAllSobolevJets H P W S hS hcore G) (hpos:∀ᵐw∂P,0<G w)
    (hi:∀(p:ℝ≥0∞) [Fact (1≤p)] (hp:p≠⊤),MemLp (fun w => (G w)⁻¹) p P) :
    HasAllSobolevJets H P W S hS hcore (fun w => (G w)⁻¹) := by
  obtain ⟨U,hG2,hU2,hGU⟩ := all_sobolev_first_graph H P W S hS hcore G hG 2 (by simp) D hg
  have hF := all_sobolev_congr H P W S hS hcore G _ hG hG2.coeFn_toLp.symm
  have hp:∀ᵐw∂P,0<hG2.toLp G w := by
    filter_upwards [hG2.coeFn_toLp,hpos] with w hw hp
    rwa [hw]
  have hi2 (p:ℝ≥0∞) [Fact (1≤p)] (hp:p≠⊤) :
      MemLp (fun w => (hG2.toLp G w)⁻¹^2) p P := by
    letI:Fact (1≤p*2) := ⟨one_le_mul Fact.out (by norm_num)⟩
    have hpt:p*2≠⊤ := ENNReal.mul_ne_top hp (by norm_num)
    have hs := memLp_norm_power P p 2 (by omega) (fun w => (G w)⁻¹) (hi (p*2) hpt)
    simp only [Real.norm_eq_abs,sq_abs] at hs
    apply hs.ae_eq
    filter_upwards [hG2.coeFn_toLp] with w hw
    rw [hw]
  have hs := all_sobolev_reciprocal_square H P W S hS hcore hdense D hD hg
    (hG2.toLp G) (hU2.toLp U) hGU hF hp hi2
  have hs' : HasAllSobolevJets H P W S hS hcore (fun w => (G w)⁻¹^2) := by
    apply all_sobolev_congr H P W S hS hcore _ _ hs
    filter_upwards [hG2.coeFn_toLp] with w hw
    rw [hw]
  have hprod := all_sobolev_product H P W S hS hcore hdense G _ hG hs'
  apply all_sobolev_congr H P W S hS hcore _ _ hprod
  filter_upwards [hpos] with w hw
  field_simp
end Asakura.Chapter12
#print axioms Asakura.Chapter12.all_sobolev_reciprocal

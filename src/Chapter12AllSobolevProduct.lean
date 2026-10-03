import Chapter12AllSobolevComposition
import Chapter12AllSobolevLinear
import Chapter12DerivativeGrowthProduct
import Chapter12LinearCylinder

open MeasureTheory ProbabilityTheory Set ENNReal
open scoped ContDiff
namespace Asakura.Chapter12
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} [MeasurableSpace Ω]
    (H : RealHilbertSpaceData) [Nontrivial H] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀u∈S,HasLaw (W u : Ω → ℝ) (gaussianReal 0 ⟨‖u‖^2,sq_nonneg _⟩) P)
    (hdense : ∀ (q : ℝ≥0∞) [Fact (1≤q)] (hq : q≠⊤),
      DenseRange (fun c : SmoothCylinder H => c.valueLp P W S hS hcore q hq))

include hdense

theorem all_sobolev_square (F : Ω → ℝ) (hF : HasAllSobolevJets H P W S hS hcore F) :
    HasAllSobolevJets H P W S hS hcore (fun w => (F w)^2) := by
  have hB := iterated_polynomial_growth_mul (fun x:ℝ => x) (fun x:ℝ => x) contDiff_id contDiff_id
    (linear_map_all_derivatives_growth (ContinuousLinearMap.id ℝ ℝ))
    (linear_map_all_derivatives_growth (ContinuousLinearMap.id ℝ ℝ))
  simpa only [Function.comp_def,pow_two] using all_sobolev_smooth_composition
    H P W S hS hcore hdense (fun x:ℝ => x*x) (contDiff_id.mul contDiff_id) hB F hF

theorem all_sobolev_product (F G : Ω → ℝ) (hF : HasAllSobolevJets H P W S hS hcore F)
    (hG : HasAllSobolevJets H P W S hS hcore G) :
    HasAllSobolevJets H P W S hS hcore (fun w => F w*G w) := by
  have hsum := all_sobolev_square H P W S hS hcore hdense _
    (all_sobolev_add H P W S hS hcore F G hF hG)
  have hf2 := all_sobolev_square H P W S hS hcore hdense F hF
  have hg2 := all_sobolev_square H P W S hS hcore hdense G hG
  have hx := all_sobolev_smul H P W S hS hcore _
    (all_sobolev_add H P W S hS hcore _ _
      (all_sobolev_add H P W S hS hcore _ _ hsum (all_sobolev_smul H P W S hS hcore _ hf2 (-1)))
      (all_sobolev_smul H P W S hS hcore _ hg2 (-1))) (1/2)
  apply all_sobolev_congr H P W S hS hcore _ _ hx
  exact Filter.Eventually.of_forall (fun w => by ring)
end Asakura.Chapter12
#print axioms Asakura.Chapter12.all_sobolev_product

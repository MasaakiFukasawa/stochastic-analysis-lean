import Chapter12MalliavinReciprocal
import Chapter12ClosedProductRaw

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

theorem closed_reciprocal_raw {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Nontrivial H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀ h ∈ S, HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (D : Lp ℝ p P →ₗ.[ℝ] Lp H p P) (hD : D.IsClosed)
    (hg : (D.graph : Set _) = closure (range (cylinderPair P W S hS hcore p hp)))
    (F : Ω → ℝ) (U : Ω → H) (hF : MemLp F p P) (hU : MemLp U p P)
    (hFU : (hF.toLp _,hU.toLp _) ∈ D.graph) (hpos : ∀ᵐ w ∂P, 0 < F w)
    (hi : MemLp (fun w => (F w)⁻¹) p P)
    (hdi : MemLp (fun w => (-(F w)⁻¹^2) • U w) p P) :
    (hi.toLp _,hdi.toLp _) ∈ D.graph := by
  have he : (fun w => (hF.toLp F w)⁻¹) =ᵐ[P] (fun w => (F w)⁻¹) := by
    filter_upwards [hF.coeFn_toLp] with w hw
    rw [hw]
  have hue : (fun w => (-(hF.toLp F w)⁻¹^2) • hU.toLp U w) =ᵐ[P]
      (fun w => (-(F w)⁻¹^2) • U w) := by
    filter_upwards [hF.coeFn_toLp,hU.coeFn_toLp] with w hw hu
    rw [hw,hu]
  have hi' := hi.ae_eq he.symm
  have hdi' := hdi.ae_eq hue.symm
  have hh := closed_malliavin_reciprocal_chain P W S hS hcore p hp D hD hg
    (hF.toLp _) (hU.toLp _) hFU
    (by filter_upwards [hF.coeFn_toLp,hpos] with w hw hp; rwa [hw]) hi' hdi'
  have hv : hi'.toLp _ = hi.toLp _ := Lp.ext (hi'.coeFn_toLp.trans (he.trans hi.coeFn_toLp.symm))
  have hu : hdi'.toLp _ = hdi.toLp _ := Lp.ext (hdi'.coeFn_toLp.trans (hue.trans hdi.coeFn_toLp.symm))
  rwa [hv,hu] at hh

/-- The inverse-square derivative factor is integrable by two Holder
steps. This is the moment requirement used for the Asian denominator. -/
theorem reciprocal_derivative_memLp {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (P : Measure Ω) (p q r : ℝ≥0∞)
    [ENNReal.HolderTriple r r q] [ENNReal.HolderTriple q q p]
    (F : Ω → ℝ) (U : Ω → H)
    (hi : MemLp (fun w => (F w)⁻¹) r P) (hU : MemLp U q P) :
    MemLp (fun w => (-(F w)⁻¹^2) • U w) p P := by
  have hs : MemLp (fun w => (F w)⁻¹^2) q P := by
    convert hi.mul hi using 1
    funext w
    exact pow_two _
    infer_instance
  exact hs.neg.smul hU

end Asakura.Chapter12

import Chapter13ClosedNumeraire
import Chapter13PricingBayes
import Chapter13MartingaleClosure

open MeasureTheory Set
namespace Asakura.Chapter13
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

/-- Bond numeraire change, with integrability of the new prices proved by Bayes. -/
theorem bond_numeraire_martingale {Ω ι:Type*} {m:MeasurableSpace Ω} [Preorder ι]
    (P:Measure Ω) [IsProbabilityMeasure P]
    (F:ι → MeasurableSpace Ω) (hF:Monotone F) (hle:∀t,F t≤m)
    (Z:Ω → ℝ) (hZm:Measurable Z) (hZi:Integrable Z P) (hZp:∀ᵐw∂P,0<Z w)
    (B bond X:ι → Ω → ℝ) (hB:∀t w,B t w≠0)
    (hNm:∀t,StronglyMeasurable[F t] (fun w => bond t w/B t w))
    (hN:∀t,P[Z|F t]=ᵐ[P] (fun w => bond t w/B t w))
    (hXm:∀t,StronglyMeasurable[F t] (fun w => X t w/B t w))
    (hXi:∀t,Integrable (fun w => X t w/B t w) P)
    (hX:∀s t,s≤t → P[(fun w => X t w/B t w)|F s]=ᵐ[P] (fun w => X s w/B s w)) :
    let c:=∫w,Z w∂P
    let Q:=P.withDensity (fun w => ENNReal.ofReal (Z w/c))
    IsProbabilityMeasure Q ∧ (∀t,Integrable (fun w => X t w/bond t w) Q) ∧
    (∀s t,s≤t → Q[(fun w => X t w/bond t w)|F s]=ᵐ[Q] (fun w => X s w/bond s w)) := by
  have he t : (fun w => (X t w/B t w)/(bond t w/B t w))=(fun w => X t w/bond t w) := by
    funext w
    exact div_div_div_cancel_right₀ (hB t w) _ _
  have h:=closed_numeraire_martingale P F hF hle Z hZm hZi hZp
    (fun t w => bond t w/B t w) hNm hN (fun t w => X t w/B t w) hXm hXi hX
  simpa only [he] using h

/-- A term rate is an affine function of the bond-price ratio under its forward measure. -/
theorem term_rate_forward_martingale {Ω ι:Type*} {m:MeasurableSpace Ω} [Preorder ι]
    (Q:Measure Ω) [IsProbabilityMeasure Q]
    (F:ι → MeasurableSpace Ω) (hle:∀t,F t≤m)
    (R:ι → Ω → ℝ) (δ:ℝ)
    (hi:∀t,Integrable (R t) Q)
    (hm:∀s t,s≤t → Q[R t|F s]=ᵐ[Q] R s) :
    (∀t,Integrable (fun w => (R t w-1)/δ) Q) ∧
    (∀s t,s≤t → Q[(fun w => (R t w-1)/δ)|F s]=ᵐ[Q] (fun w => (R s w-1)/δ)) := by
  refine ⟨fun t => ((hi t).sub (integrable_const 1)).div_const δ,?_⟩
  intro s t hst
  have h:=(affine_martingale_identity Q F hle R hi hm δ⁻¹ (-δ⁻¹)).2 s t hst
  convert h using 1 <;> congr 1 <;> funext w <;> ring

end Asakura.Chapter13
#print axioms Asakura.Chapter13.bond_numeraire_martingale
#print axioms Asakura.Chapter13.term_rate_forward_martingale

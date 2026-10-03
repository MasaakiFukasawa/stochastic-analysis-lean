import Chapter13MartingaleClosure

open MeasureTheory Set
namespace Asakura.Chapter13
set_option maxHeartbeats 1800000

/-- The corrected risk-neutral formula is equivalent to a closed discounted
martingale. No integrability of the bank account ratio is needed. -/
theorem closed_bond_pricing_martingale {Ω ι:Type*} {m:MeasurableSpace Ω} [Preorder ι]
    (P:Measure Ω) [IsProbabilityMeasure P] (F:ι → MeasurableSpace Ω)
    (hF:Monotone F) (hle:∀t,F t≤m)
    (B p:ι → Ω → ℝ) (hB:∀t w,B t w≠0) (Z:Ω → ℝ) (hi:Integrable Z P)
    (he:∀t,p t=ᵐ[P] (fun w => B t w*P[Z|F t] w)) :
    (∀t,Integrable (fun w => p t w/B t w) P) ∧
    (∀s t,s≤t → P[(fun w => p t w/B t w)|F s]=ᵐ[P] (fun w => p s w/B s w)) := by
  have hh t:(fun w => p t w/B t w)=ᵐ[P] P[Z|F t] := by
    filter_upwards [he t] with w hw
    rw [hw]
    exact mul_div_cancel_left₀ _ (hB t w)
  refine ⟨fun t => (integrable_condExp (μ:=P) (m:=F t) (f:=Z)).congr (hh t).symm,?_⟩
  intro s t hst
  exact (condExp_congr_ae (hh t)).trans ((condExp_condExp_of_le (hF hst) (hle t)).trans (hh s).symm)
end Asakura.Chapter13
#print axioms Asakura.Chapter13.closed_bond_pricing_martingale

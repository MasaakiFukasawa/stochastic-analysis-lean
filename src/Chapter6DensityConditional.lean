import FullAuditBayes

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
namespace Asakura.Chapter6
open Asakura.FullAudit
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/-- Conditional density at the observation time transfers an adapted integrable
variable from Q to P. The integrability of the product is derived, not assumed. -/
theorem conditional_density_product
    {Ω : Type*} {G m : MeasurableSpace Ω}
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hG : G ≤ m) (d : Ω → ℝ≥0) (hd : Measurable d)
    (hdi : Integrable (fun w => (d w : ℝ)) P)
    (hQ : Q = P.withDensity (fun w => (d w : ℝ≥0∞)))
    (X : Ω → ℝ) (hX : StronglyMeasurable[G] X) (hi : Integrable X Q) :
    Integrable (fun w => P[(fun w => (d w : ℝ))|G] w * X w) P ∧
    P[(fun w => (d w : ℝ)*X w)|G] =ᵐ[P]
      (fun w => P[(fun w => (d w : ℝ))|G] w * X w)  := by
  letI : MeasurableSpace Ω := m
  have hDX : Integrable (fun w => (d w : ℝ)*X w) P := by
    rw [hQ] at hi
    simpa only [smul_eq_mul] using (integrable_withDensity_iff_integrable_coe_smul hd).mp hi
  have he := unbounded_pullout_right P hG (fun w => (d w : ℝ)) X hX hDX hdi
  exact ⟨integrable_condExp.congr he,he⟩

/-- The deterministic-time identity behind the measure-change lemma.
Both conditional expectations and the density are actual conditional expectations. -/
theorem density_conditional_transport
    {Ω : Type*} {G H m : MeasurableSpace Ω}
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hGH : G ≤ H) (hH : H ≤ m) (d : Ω → ℝ≥0) (hd : Measurable d)
    (hdi : Integrable (fun w => (d w : ℝ)) P)
    (hdpos : ∀ᵐ w ∂P, 0 < (d w : ℝ))
    (hQ : Q = P.withDensity (fun w => (d w : ℝ≥0∞)))
    (X : Ω → ℝ) (hX : StronglyMeasurable[H] X) (hi : Integrable X Q) :
    P[(fun w => P[(fun w => (d w : ℝ))|H] w * X w)|G] =ᵐ[P]
      (fun w => P[(fun w => (d w : ℝ))|G] w * Q[X|G] w)  := by
  letI : MeasurableSpace Ω := m
  have hp := (conditional_density_product P Q hH d hd hdi hQ X hX hi).2
  have hc := condExp_congr_ae (m := G) hp
  have ht := condExp_condExp_of_le hGH hH (f := fun w => (d w : ℝ)*X w) (μ := P)
  have hb := bayes_written_with_unbounded_pullout P Q (hGH.trans hH) d hd hdi hdpos hQ X hi
  have hpos := exercise_ce_strictly_positive P (hGH.trans hH) hdi hdpos
  filter_upwards [hc,ht,hb,hpos] with w hc ht hb hz
  rw [← hc,ht,hb]
  exact (mul_div_cancel₀ _ (ne_of_gt hz)).symm

end Asakura.Chapter6

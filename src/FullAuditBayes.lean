import FullAuditUnboundedPullout
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal
namespace Asakura.FullAudit
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

/-- Bayes' formula along the written set-integral comparison. Integrability
 is required under Q only; weighted integrability under P is proved from
 the density. The unbounded pull-out theorem is explicitly used at the end. -/
theorem bayes_written_with_unbounded_pullout {Ω : Type*} {G m : MeasurableSpace Ω}
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hG : G ≤ m) (d : Ω → ℝ≥0) (hd : Measurable d)
    (hdi : Integrable (fun ω => (d ω : ℝ)) P)
    (hdpos : ∀ᵐ ω ∂P, 0 < (d ω : ℝ))
    (hQ : Q = P.withDensity (fun ω => (d ω : ℝ≥0∞)))
    (X : Ω → ℝ) (hX : Integrable X Q) :
    Q[X|G] =ᵐ[P] fun ω => P[(fun ω => (d ω:ℝ)*X ω)|G] ω / P[(fun ω => (d ω:ℝ))|G] ω := by
  letI : MeasurableSpace Ω := m
  let D := fun ω => (d ω : ℝ)
  let Y := Q[X|G]
  have hYi : Integrable Y Q := integrable_condExp
  have hDX : Integrable (fun ω => D ω*X ω) P := by
    have h := hX
    rw [hQ] at h
    simpa only [smul_eq_mul] using (integrable_withDensity_iff_integrable_coe_smul hd).mp h
  have hDY : Integrable (fun ω => D ω*Y ω) P := by
    have h := hYi
    rw [hQ] at h
    simpa only [smul_eq_mul] using (integrable_withDensity_iff_integrable_coe_smul hd).mp h
  have hchange (f : Ω → ℝ) (A : Set Ω) (hA : MeasurableSet A) :
      (∫ ω in A, f ω ∂Q) = ∫ ω in A, D ω*f ω ∂P := by
    rw [hQ]
    exact setIntegral_withDensity_eq_setIntegral_smul hd f hA
  have heq : P[(fun ω => D ω*Y ω)|G] =ᵐ[P] P[(fun ω => D ω*X ω)|G] := by
    apply ae_eq_condExp_of_forall_setIntegral_eq hG hDX
      (fun A _ _ => integrable_condExp.integrableOn) _ stronglyMeasurable_condExp.aestronglyMeasurable
    intro A hA _
    rw [setIntegral_condExp hG hDY hA,← hchange Y A (hG A hA),← hchange X A (hG A hA)]
    exact setIntegral_condExp hG hX hA
  have hpull := unbounded_pullout_right P hG D Y stronglyMeasurable_condExp hDY hdi
  change P[(fun ω => D ω*Y ω)|G] =ᵐ[P] fun ω => P[D|G] ω*Y ω at hpull
  have hpos := exercise_ce_strictly_positive P hG hdi hdpos
  filter_upwards [heq,hpull,hpos] with ω hEq hPull hPos
  change Y ω = _
  apply (eq_div_iff (ne_of_gt hPos)).mpr
  rw [← hEq, hPull]
  ring

/-- Real-valued densities may be modified on their null negative set.
 This wrapper restores the original manuscript's almost-everywhere positivity
 hypothesis instead of requiring positivity at every point. -/
theorem bayes_real_density {Ω : Type*} {G m : MeasurableSpace Ω}
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hG : G ≤ m) (D : Ω → ℝ) (hDm : Measurable D) (hDi : Integrable D P)
    (hDpos : ∀ᵐ ω ∂P, 0 < D ω)
    (hQ : Q = P.withDensity (fun ω => ENNReal.ofReal (D ω)))
    (X : Ω → ℝ) (hX : Integrable X Q) :
    Q[X|G] =ᵐ[P] fun ω => P[(fun ω => D ω*X ω)|G] ω / P[D|G] ω := by
  letI : MeasurableSpace Ω := m
  let d := fun ω => (D ω).toNNReal
  have hdm : Measurable d := by fun_prop
  have hdeq : (fun ω => (d ω:ℝ)) =ᵐ[P] D := by
    filter_upwards [hDpos] with ω hω
    exact Real.coe_toNNReal _ hω.le
  have hdi : Integrable (fun ω => (d ω:ℝ)) P := hDi.congr hdeq.symm
  have hdpos : ∀ᵐ ω ∂P, 0 < (d ω:ℝ) := by
    filter_upwards [hdeq,hDpos] with ω he hp
    rwa [he]
  have hbase := bayes_written_with_unbounded_pullout P Q hG d hdm hdi hdpos hQ X hX
  have hcD := condExp_congr_ae (m := G) hdeq
  have hcDX := condExp_congr_ae (m := G) (hdeq.mul (EventuallyEq.refl _ X))
  change P[(fun ω => (d ω:ℝ)*X ω)|G] =ᵐ[P] P[(fun ω => D ω*X ω)|G] at hcDX
  filter_upwards [hbase,hcD,hcDX] with ω hb hd hx
  rw [hb,hd,hx]

end Asakura.FullAudit

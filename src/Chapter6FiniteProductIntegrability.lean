import FullAuditUnboundedPullout
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Function.L1Space.Integrable

open MeasureTheory Set Filter
open scoped NNReal ENNReal
namespace Asakura.Chapter6
open Asakura.FullAudit
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

/-- A mean-one conditional factor leaves the earlier sigma algebra unchanged
under density weighting. This proves integrability before using pull-out. -/
theorem conditional_unit_density_trim {Ω : Type*} {G m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (hG : G ≤ m)
    (d : Ω → ℝ≥0) (hi : Integrable (fun w => (d w : ℝ)) P)
    (he : P[(fun w => (d w : ℝ))|G] =ᵐ[P] (fun _ => (1:ℝ))) :
    (P.withDensity (fun w => (d w : ℝ≥0∞))).trim hG = P.trim hG := by
  apply @Measure.ext Ω G
  intro A hA
  rw [trim_measurableSet_eq hG hA,trim_measurableSet_eq hG hA,
    withDensity_apply _ (hG A hA)]
  have hiA := hi.integrableOn (s := A)
  have hIA : (∫ w in A,(d w : ℝ) ∂P) = (P A).toReal := by
    rw [← setIntegral_condExp hG hi hA,integral_congr_ae (ae_restrict_of_ae he)]
    simp [measureReal_def]
  have hh := ofReal_integral_eq_lintegral_ofReal hiA (ae_of_all _ (fun w => (d w).coe_nonneg))
  simpa only [hIA,ENNReal.ofReal_toReal (measure_ne_top P A),ENNReal.ofReal_coe_nnreal] using hh.symm

/-- The conditional expectation and integrability of a product follow from
conditional mean one, even when the earlier factor is unbounded. -/
theorem conditional_unit_factor_product {Ω : Type*} {G m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (hG : G ≤ m)
    (d : Ω → ℝ≥0) (hd : Measurable d)
    (hi : Integrable (fun w => (d w : ℝ)) P)
    (he : P[(fun w => (d w : ℝ))|G] =ᵐ[P] (fun _ => (1:ℝ)))
    (X : Ω → ℝ) (hX : StronglyMeasurable[G] X) (hXi : Integrable X P) :
    Integrable (fun w => X w*(d w : ℝ)) P ∧
      P[(fun w => X w*(d w : ℝ))|G] =ᵐ[P] X := by
  have htrim := conditional_unit_density_trim P hG d hi he
  have hq : Integrable X (P.withDensity (fun w => (d w : ℝ≥0∞))) := by
    apply integrable_of_integrable_trim hG
    rw [htrim]
    exact Integrable.trim hG hXi hX
  have hprod : Integrable (fun w => X w*(d w : ℝ)) P := by
    have hh := (integrable_withDensity_iff_integrable_coe_smul hd).mp hq
    simpa only [smul_eq_mul,mul_comm] using hh
  refine ⟨hprod,?_⟩
  have hh := unbounded_pullout_by_restriction P hG X (fun w => (d w : ℝ)) hX hprod hi
  filter_upwards [hh,he] with w hw hew
  change P[(fun w => X w*(d w : ℝ))|G] w = X w*P[(fun w => (d w : ℝ))|G] w at hw
  rw [hw,hew,mul_one]

end Asakura.Chapter6

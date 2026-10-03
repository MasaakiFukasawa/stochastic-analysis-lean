import Chapter13ParameterStopping
import Chapter13AccumulatedEnergy

open MeasureTheory Set
namespace Asakura.Chapter13
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- Integration in maturity preserves progressiveness of the accumulated
square-energy driver. -/
theorem parameter_energy_progressive {Ω E:Type*} [MeasurableSpace E]
    (F:HalfClosedTime → MeasurableSpace Ω) (μ:Measure E) [SigmaFinite μ]
    (b:ℝ) (H:E × (Ω × ℝ) → ℝ)
    (hp:@Measurable _ _
      ((inferInstance : MeasurableSpace E).prod (progressiveSpace (fun t:Icc (0:ℝ) b => F (realTimeClamp t.val)))) inferInstance
      (fun z:E × (Ω × Icc (0:ℝ) b) => H (z.1,(z.2.1,z.2.2.val)))) :
    @Measurable _ _ (progressiveSpace (fun t:Icc (0:ℝ) b => F (realTimeClamp t.val))) inferInstance
      (fun z:Ω × Icc (0:ℝ) b => ∫x,H (x,(z.1,z.2.val))^2∂μ) := by
  letI:MeasurableSpace (Ω × Icc (0:ℝ) b):=progressiveSpace (fun t:Icc (0:ℝ) b => F (realTimeClamp t.val))
  exact (hp.pow_const 2).stronglyMeasurable.integral_prod_left'.measurable

/-- Construct the energy primitive directly from the parameter-dependent
coefficient. Its measurability and time integrability are conclusions. -/
theorem parameter_energy_constructed {Ω E:Type*} [MeasurableSpace E]
    (F:HalfClosedTime → MeasurableSpace Ω) (hF:Monotone F)
    (μ:Measure E) [SigmaFinite μ] (R:ℝ) (hR:0≤R) (H:E × (Ω × ℝ) → ℝ)
    (hp:@Measurable _ _
      ((inferInstance : MeasurableSpace E).prod (progressiveSpace (fun t:Icc (0:ℝ) R => F (realTimeClamp t.val)))) inferInstance
      (fun z:E × (Ω × Icc (0:ℝ) R) => H (z.1,(z.2.1,z.2.2.val))))
    (hi:∀w,Integrable (fun z:E × ℝ => H (z.1,(w,z.2))^2) (μ.prod (volume.restrict (Ioc 0 R)))) :
    ∃C:HalfClosedTime → Ω → ℝ,
      (∀t,Measurable[F t] (C t)) ∧ (∀w,Continuous (fun t => C t w)) ∧
      (∀w,C ⊥ w=0) ∧ (∀t w,C t w≤∫r in 0..R,∫x,H (x,(w,r))^2∂μ) ∧
      ∀t w,C t w=∫r in 0..(finitePrefixTime R hR t).val,∫x,H (x,(w,r))^2∂μ := by
  apply accumulated_energy_constructed F hF R hR (fun z => ∫x,H (x,z)^2∂μ)
  · exact parameter_energy_progressive F μ R H hp
  · exact fun w => (hi w).integral_prod_right
  · intro w r
    exact integral_nonneg (fun x => sq_nonneg _)
end Asakura.Chapter13
#print axioms Asakura.Chapter13.parameter_energy_progressive
#print axioms Asakura.Chapter13.parameter_energy_constructed

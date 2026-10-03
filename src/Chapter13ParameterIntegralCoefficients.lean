import Chapter13BoundedCoefficient
import Chapter13ParameterEnergy

open MeasureTheory Set
namespace Asakura.Chapter13
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false

/-- Integration over a finite maturity interval preserves all coefficient
hypotheses needed to construct the Brownian exponent. -/
theorem parameter_integral_coefficients {Ω E:Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (F:HalfClosedTime → MeasurableSpace Ω) (μ:Measure E) [IsFiniteMeasure μ]
    (H:E × (Ω × ℝ) → ℝ) (hm:Measurable H)
    (hp:∀b,0<b → @Measurable _ _
      ((inferInstance : MeasurableSpace E).prod (progressiveSpace (fun t:Icc (0:ℝ) b => F (realTimeClamp t.val)))) inferInstance
      (fun z:E × (Ω × Icc (0:ℝ) b) => H (z.1,(z.2.1,z.2.2.val))))
    (hb:∀w b,0≤b → ∃K:ℝ,0≤K ∧ ∀x r,r∈Icc 0 b → |H (x,(w,r))|≤K) :
    let J:=fun z:Ω × ℝ => ∫x,H (x,z)∂μ
    Measurable J ∧
      (∀b,0<b → @Measurable _ _ (progressiveSpace (fun t:Icc (0:ℝ) b => F (realTimeClamp t.val))) inferInstance
        (fun z:Ω × Icc (0:ℝ) b => J (z.1,z.2.val))) ∧
      (∀w b,0≤b → IntervalIntegrable (fun r => J (w,r)^2) volume 0 b) ∧
      (∀w b,0≤b → IntervalIntegrable (fun r => J (w,r)) volume 0 b) := by
  intro J
  have hJm:Measurable J := hm.stronglyMeasurable.integral_prod_left'.measurable
  have hJp b (hb0:0<b):@Measurable _ _ (progressiveSpace (fun t:Icc (0:ℝ) b => F (realTimeClamp t.val))) inferInstance
      (fun z:Ω × Icc (0:ℝ) b => J (z.1,z.2.val)) := by
    letI:MeasurableSpace (Ω × Icc (0:ℝ) b):=progressiveSpace (fun t:Icc (0:ℝ) b => F (realTimeClamp t.val))
    exact (hp b hb0).stronglyMeasurable.integral_prod_left'.measurable
  have hJb w b (hb0:0≤b):∃K:ℝ,0≤K ∧ ∀r∈Icc 0 b,|J (w,r)|≤K := by
    obtain ⟨K,hK,hbound⟩:=hb w b hb0
    refine ⟨K*μ.real univ,mul_nonneg hK (measureReal_nonneg),?_⟩
    intro r hr
    have hh:=norm_integral_le_of_norm_le_const (μ:=μ) (f:=fun x => H (x,(w,r)))
      (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hbound x r hr)
    simpa only [J,Real.norm_eq_abs] using hh
  have hJ2:=bounded_coefficient_square J hJm hJb
  refine ⟨hJm,hJp,hJ2,?_⟩
  intro w b hb0
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hb0]
  have hl:MemLp (fun r => J (w,r)) 2 (volume.restrict (Ioc 0 b)) :=
    (memLp_two_iff_integrable_sq (hJm.comp measurable_prodMk_left).aestronglyMeasurable).mpr
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hb0).mp (hJ2 w b hb0))
  exact hl.integrable (by norm_num)
end Asakura.Chapter13
#print axioms Asakura.Chapter13.parameter_integral_coefficients

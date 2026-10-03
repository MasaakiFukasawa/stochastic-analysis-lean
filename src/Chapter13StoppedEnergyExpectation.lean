import Chapter13FubiniEnergy

open MeasureTheory Set
namespace Asakura.Chapter13
set_option maxHeartbeats 1800000

/-- A pathwise bound on accumulated stopped energy gives the required
integrability over probability and both parameter/time variables. -/
theorem bounded_path_energy_integrable {Ω S:Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    (P:Measure Ω) [IsProbabilityMeasure P] (ν:Measure S) [SigmaFinite ν]
    (G:Ω × S → ℝ) (hm:Measurable G) (hp:∀z,0≤G z)
    (hi:∀ᵐw∂P,Integrable (fun s => G (w,s)) ν)
    (K:ℝ) (hb:∀ᵐw∂P,(∫s,G (w,s)∂ν)≤K) :
    Integrable G (P.prod ν) ∧ (∫z,G z∂P.prod ν)≤K := by
  have hnorm:∀w,(∫s,‖G (w,s)‖∂ν)=(∫s,G (w,s)∂ν) := by
    intro w
    simp only [Real.norm_eq_abs,abs_of_nonneg (hp _)]
  have hme:Measurable (fun w => ∫s,G (w,s)∂ν) :=
    (show StronglyMeasurable (Function.uncurry (fun w s => G (w,s))) from hm.stronglyMeasurable).integral_prod_right.measurable
  have he:Integrable (fun w => ∫s,G (w,s)∂ν) P := by
    apply (integrable_const K).mono' hme.aestronglyMeasurable
    filter_upwards [hb] with w hw
    have hn:0≤∫s,G (w,s)∂ν := integral_nonneg (fun s => hp (w,s))
    simpa only [Real.norm_eq_abs,abs_of_nonneg hn] using hw
  have hG:Integrable G (P.prod ν) := (integrable_prod_iff hm.aestronglyMeasurable).mpr
    ⟨hi,by simpa only [hnorm] using he⟩
  refine ⟨hG,?_⟩
  rw [integral_prod _ hG]
  simpa using integral_mono_ae he (integrable_const K) hb
end Asakura.Chapter13
#print axioms Asakura.Chapter13.bounded_path_energy_integrable

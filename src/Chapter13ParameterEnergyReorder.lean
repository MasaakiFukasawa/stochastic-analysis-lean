import Chapter13StoppedEnergyExpectation

open MeasureTheory Set
namespace Asakura.Chapter13
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

/-- Convert pathwise stopped-energy control into the parameter × probability
× time integrability required by the Brownian stochastic Fubini theorem. -/
theorem parameter_energy_reorder {Ω E S:Type*} [MeasurableSpace Ω] [MeasurableSpace E] [MeasurableSpace S]
    (P:Measure Ω) [IsProbabilityMeasure P] (μ:Measure E) [SigmaFinite μ]
    (ν:Measure S) [SigmaFinite ν] (H:E × (Ω × S) → ℝ) (hm:Measurable H)
    (hi:∀ᵐw∂P,Integrable (fun z:E × S => H (z.1,(w,z.2))^2) (μ.prod ν))
    (K:ℝ) (hb:∀ᵐw∂P,(∫z:E × S,H (z.1,(w,z.2))^2∂μ.prod ν)≤K) :
    Integrable (fun z => H z^2) (μ.prod (P.prod ν)) := by
  have hG:Measurable (fun z:Ω × (E × S) => H (z.2.1,(z.1,z.2.2))^2) :=
    (hm.comp ((measurable_fst.comp measurable_snd).prodMk
      (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))).pow_const 2
  have hI:Integrable (fun z:Ω × (E × S) => H (z.2.1,(z.1,z.2.2))^2) (P.prod (μ.prod ν)) :=
    (bounded_path_energy_integrable P (μ.prod ν) _ hG (fun _ => sq_nonneg _) hi K hb).1
  have hI1:Integrable (fun z:(Ω × E) × S => H (z.1.2,(z.1.1,z.2))^2) ((P.prod μ).prod ν) :=
    ((measurePreserving_prodAssoc P μ ν).integrable_comp_emb MeasurableEquiv.prodAssoc.measurableEmbedding).mpr hI
  have hswap:MeasurePreserving (Prod.map (Prod.swap : E × Ω → Ω × E) (id:S → S))
      ((μ.prod P).prod ν) ((P.prod μ).prod ν) := (Measure.measurePreserving_swap (μ:=μ) (ν:=P)).prod (MeasurePreserving.id ν)
  have hI2:Integrable (fun z:(E × Ω) × S => H (z.1.1,(z.1.2,z.2))^2) ((μ.prod P).prod ν) :=
    hswap.integrable_comp_of_integrable hI1
  exact ((measurePreserving_prodAssoc μ P ν).integrable_comp_emb MeasurableEquiv.prodAssoc.measurableEmbedding).mp hI2
end Asakura.Chapter13
#print axioms Asakura.Chapter13.parameter_energy_reorder

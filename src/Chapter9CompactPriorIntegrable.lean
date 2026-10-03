import Chapter9CompactMixtureContinuity

open MeasureTheory Set
namespace Asakura.Chapter9

 theorem compact_prior_integrable {E V : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (μ : Measure E) [IsFiniteMeasure μ] (K : Set E) (hK : IsCompact K)
    (hμ : ∀ᵐ x ∂μ,x∈K) (f : E → V) (hf : Continuous f) : Integrable f μ := by
  have h := hf.continuousOn.integrableOn_compact hK (μ := μ)
  rwa [IntegrableOn,Measure.restrict_eq_self_of_ae_mem hμ] at h
end Asakura.Chapter9

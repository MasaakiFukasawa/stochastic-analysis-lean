import Chapter9CompactSupportDerivative
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter9
set_option maxHeartbeats 800000

/-- A bounded derivative is integrable up to the possibly undefined lower
endpoint. Only the right-hand limit there is needed. -/
theorem bounded_derivative_endpoint_integral (F G : ℝ → ℝ) (a b l C : ℝ) (hab : a<b)
    (hD : ∀ t∈Ioc a b,HasDerivAt F (G t) t)
    (hbound : ∀ t∈Ioc a b,‖G t‖≤C) (hlim : Tendsto F (𝓝[>] a) (𝓝 l)) :
    IntervalIntegrable G volume a b ∧ (∫ t in a..b,G t)=F b-l := by
  have hd : IntegrableOn (deriv F) (Ioc a b) := by
    apply Integrable.of_bound (measurable_deriv F).aestronglyMeasurable C
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [(hD t ht).deriv]
    exact hbound t ht
  have he : deriv F =ᵐ[volume.restrict (Ioc a b)] G := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact (hD t ht).deriv
  have hi : IntervalIntegrable G volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le).mpr (hd.congr he)
  refine ⟨hi,intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hab
    (fun t ht => hD t ⟨ht.1,ht.2.le⟩) hi hlim ?_⟩
  exact (hD b ⟨hab,le_rfl⟩).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
end Asakura.Chapter9

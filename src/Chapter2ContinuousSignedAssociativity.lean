import Chapter2SignedDensityIdentification
import Mathlib.MeasureTheory.Integral.IntegrableOn

open MeasureTheory Set Filter
open scoped Topology ENNReal Classical
namespace Asakura.Chapter2Complete
open Asakura.FullAudit
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

theorem continuous_integrable_compact_support (μ : Measure ℝ) [IsFiniteMeasure μ]
    (a b : ℝ) (f : ℝ → ℝ) (hf : ContinuousOn f (Icc a b))
    (hs : ∀ᵐ r ∂μ, r ∈ Icc a b) : Integrable f μ := by
  have h := hf.integrableOn_compact isCompact_Icc (μ := μ)
  change Integrable f (μ.restrict (Icc a b)) at h
  rwa [Measure.restrict_eq_self_of_ae_mem hs] at h

/-- The finite-variation part of associativity, including membership of
both iterated integrands, for continuous functions on the original
finite interval. The signed measure of the inner integral is constructed. -/
theorem continuous_signed_cumulative_associativity
    (ν : SignedMeasure ℝ) (a b : ℝ) (H G : ℝ → ℝ)
    (hHm : Measurable H) (hGm : Measurable G)
    (hH : ContinuousOn H (Icc a b)) (hG : ContinuousOn G (Icc a b))
    (hs : ∀ᵐ r ∂ν.totalVariation, r ∈ Icc a b) :
    Integrable G ν.totalVariation ∧ Integrable H (signedWeighted ν G).totalVariation ∧
      Integrable (fun r => H r*G r) ν.totalVariation ∧
      (∀ s t, s ≤ t → signedWeighted ν G (Ioc s t) =
        signedCumulative ν G t-signedCumulative ν G s) ∧
      ∀ t, signedCumulative (signedWeighted ν G) H t =
        signedCumulative ν (fun r => H r*G r) t := by
  have hGi := continuous_integrable_compact_support ν.totalVariation a b G hG hs
  have hκs : ∀ᵐ r ∂(signedWeighted ν G).totalVariation, r ∈ Icc a b :=
    (signed_weighted_totalVariation_ac ν G hGi).ae_le hs
  have hHi := continuous_integrable_compact_support _ a b H hH hκs
  have hHGi := continuous_integrable_compact_support ν.totalVariation a b _ (hH.mul hG) hs
  refine ⟨hGi,hHi,hHGi,?_,?_⟩
  · intro s t hst
    rw [signed_weighted_apply ν G hGi _ measurableSet_Ioc,signed_cumulative_increment ν G hGi s t hst]
  · intro t
    have hi : Integrable (fun r => ((Iic t).indicator H r)*G r) ν.totalVariation := by
      have he : (fun r => ((Iic t).indicator H r)*G r) = (Iic t).indicator (fun r => H r*G r) := by
        funext r; by_cases hr : r ∈ Iic t <;> simp [hr]
      rw [he]; exact hHGi.indicator measurableSet_Iic
    have hh := signed_density_integral ν (signedWeighted ν G) G ((Iic t).indicator H)
      hGm (hHm.indicator measurableSet_Iic) hGi (hHi.indicator measurableSet_Iic) hi
      (fun E hE => signed_weighted_apply ν G hGi E hE)
    change signedIntegralRaw _ _ = signedIntegralRaw _ _
    rw [hh]
    congr 1
    funext r; by_cases hr : r ∈ Iic t <;> simp [hr]

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.continuous_signed_cumulative_associativity

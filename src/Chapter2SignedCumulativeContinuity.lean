import Chapter2SignedCumulativeVariation
import Chapter2CovarianceAbsoluteContinuity

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

theorem signed_cumulative_continuous (ν : SignedMeasure ℝ)
    [NullSingletonClass ν.totalVariation] (f : ℝ → ℝ)
    (hf : Integrable f ν.totalVariation) : Continuous (signedCumulative ν f) := by
  have hp : ν.toJordanDecomposition.posPart ≤ ν.totalVariation := by intro s; exact le_add_right le_rfl
  have hn : ν.toJordanDecomposition.negPart ≤ ν.totalVariation := by intro s; exact le_add_left le_rfl
  letI : NullSingletonClass ν.toJordanDecomposition.posPart :=
    ⟨fun r => le_antisymm ((hp {r}).trans_eq (measure_singleton r)) bot_le⟩
  letI : NullSingletonClass ν.toJordanDecomposition.negPart :=
    ⟨fun r => le_antisymm ((hn {r}).trans_eq (measure_singleton r)) bot_le⟩
  have h := (continuous_cumulative_integral _ f (hf.mono_measure hp)).sub
    (continuous_cumulative_integral _ f (hf.mono_measure hn))
  change Continuous (fun t => (∫ r, (Iic t).indicator f r ∂ν.toJordanDecomposition.posPart) -
    ∫ r, (Iic t).indicator f r ∂ν.toJordanDecomposition.negPart)
  simp_rw [integral_indicator measurableSet_Iic]
  exact h

/-- Interval Cauchy-Schwarz and the atomlessness of the first Stieltjes
measure imply continuity of the actual signed cumulative integral. -/
theorem signed_cs_cumulative_continuous
    (α β : Measure ℝ) [IsFiniteMeasure α] [IsFiniteMeasure β] [NullSingletonClass α]
    (ν : SignedMeasure ℝ)
    (hc : ∀ s t, s ≤ t → |ν (Ioc s t)| ≤ Real.sqrt (α.real (Ioc s t))*Real.sqrt (β.real (Ioc s t)))
    (f : ℝ → ℝ) (hf : Measurable f) (hfi : Integrable (fun r => f r^2) α) :
    Integrable f ν.totalVariation ∧ Continuous (signedCumulative ν f) := by
  have hν := signed_cs_absolute_continuity α β ν hc
  letI : NullSingletonClass ν.totalVariation := ⟨fun r => hν (measure_singleton r)⟩
  have hi := (signed_stieltjes_single_integral_bound α β ν hc f hf hfi).1
  exact ⟨hi,signed_cumulative_continuous ν f hi⟩

theorem signed_integral_add_smul
    {S : Type*} [MeasurableSpace S] (ν : SignedMeasure S) (f g : S → ℝ)
    (hf : Integrable f ν.totalVariation) (hg : Integrable g ν.totalVariation) (c : ℝ) :
    signedIntegralRaw ν (fun r => c*f r+g r) = c*signedIntegralRaw ν f+signedIntegralRaw ν g := by
  have hp : ν.toJordanDecomposition.posPart ≤ ν.totalVariation := by intro s; exact le_add_right le_rfl
  have hn : ν.toJordanDecomposition.negPart ≤ ν.totalVariation := by intro s; exact le_add_left le_rfl
  unfold signedIntegralRaw
  rw [integral_add ((hf.mono_measure hp).const_mul c) (hg.mono_measure hp),
    integral_add ((hf.mono_measure hn).const_mul c) (hg.mono_measure hn),integral_const_mul,integral_const_mul]
  ring

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.signed_cs_cumulative_continuous
#print axioms Asakura.Chapter2Complete.signed_integral_add_smul

import Chapter2LocalSignedIntegral

open MeasureTheory Set Filter
open scoped Topology ENNReal Classical
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

/-- The variation estimate is for the constructed process on the original
time space, not merely for an auxiliary real-time cumulative integral. -/
theorem integral_process_variation_bound
    {T : EReal} [Fact (0 ≤ T)]
    (d : ℝ) (hd : 0 ≤ d) (hdT : (d:EReal) ≤ T)
    (κ : Measure ℝ) (ξ : SignedMeasure ℝ) (hdom : ξ.totalVariation ≤ κ)
    (H : ℝ → ℝ) (hi : Integrable H κ) (I : ClosedTime T → ℝ)
    (he : ∀ t, I (min (realTimeClamp d) t) =
      signedCumulative ξ H (finitePrefixTime d hd t).val)
    (t : ClosedTime T) (ht : t ≤ realTimeClamp d) :
    pathVariation I t ≤ ∫ r in Ioc 0 (finitePrefixTime d hd t).val, |H r| ∂κ := by
  let p := fun s : ClosedTime T => (finitePrefixTime d hd s).val
  have hEq : eVariationOn I (Iic t) = eVariationOn (signedCumulative ξ H ∘ p) (Iic t) := by
    apply eVariationOn.congr
    intro s hs
    simpa only [min_eq_right (hs.trans ht),Function.comp_def,p] using he s
  have hv : eVariationOn I (Iic t) ≤ ENNReal.ofReal (∫ r in Ioc 0 (p t), |H r| ∂κ) := by
    rw [hEq]
    apply (eVariationOn.comp_le_of_monotoneOn (s := Icc 0 (p t)) (t := Iic t) (signedCumulative ξ H) p
      (fun _ _ _ _ h => finite_prefix_time_mono d hd h)
      (fun s hs => ⟨(finitePrefixTime d hd s).property.1,finite_prefix_time_mono d hd hs⟩)).trans
    apply (signed_cumulative_variation_bound ξ H (hi.mono_measure hdom) 0 (p t)).trans
    apply ENNReal.ofReal_le_ofReal
    exact integral_mono_measure (Measure.restrict_mono le_rfl hdom)
      (.of_forall (fun r => abs_nonneg _)) hi.abs.integrableOn
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hv
  simpa only [pathVariation,p,ENNReal.toReal_ofReal (integral_nonneg (fun r => abs_nonneg _))] using hh

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.integral_process_variation_bound

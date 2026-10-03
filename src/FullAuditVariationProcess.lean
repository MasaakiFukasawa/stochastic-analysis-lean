import FullAuditMartingalePathNorm
import Mathlib.Topology.EMetricSpace.VariationOnFromTo
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.FullAudit
set_option backward.isDefEq.respectTransparency false

/-- Total variation as the supremum of the continuous finite-partition sums. -/
theorem continuous_map_variation_lowerSemicontinuous {ι : Type*} [LinearOrder ι]
    [TopologicalSpace ι] [CompactSpace ι] (S : Set ι) :
    LowerSemicontinuous (fun f : C(ι,ℝ) => eVariationOn f S) := by
  unfold eVariationOn
  apply lowerSemicontinuous_iSup
  rintro ⟨n,u,hu,hs⟩
  apply Continuous.lowerSemicontinuous
  apply continuous_finset_sum
  intro j hj
  exact (continuous_eval_const (u (j+1))).edist
    (continuous_eval_const (u j))

/-- The variation at time t is measurable from observations up to t only. -/
theorem variation_process_adapted {Ω ι : Type*} [LinearOrder ι] [TopologicalSpace ι]
    [OrderTopology ι] [CompactSpace ι] [SecondCountableTopology ι]
    (F : ι → MeasurableSpace Ω) (hF : Monotone F)
    (X : ι → Ω → ℝ) (hm : ∀ t, Measurable[F t] (X t))
    (hc : ∀ ω, Continuous (fun t => X t ω)) (t : ι) :
    Measurable[F t] (fun ω => (eVariationOn (fun s => X s ω) (Iic t)).toReal) := by
  letI : MeasurableSpace Ω := F t
  letI : CompactSpace (Iic t) := isCompact_iff_compactSpace.mp (isClosed_Iic : IsClosed (Iic t)).isCompact
  let Y : Ω → C(Iic t,ℝ) := fun ω => ⟨fun s => X s ω,(hc ω).comp continuous_subtype_val⟩
  have hY : Measurable[F t] Y := ContinuousMap.measurable_iff_eval.mpr fun s =>
    (hm s).mono (hF s.property) le_rfl
  have hv := (continuous_map_variation_lowerSemicontinuous (univ : Set (Iic t))).measurable.comp hY
  have he (ω : Ω) : eVariationOn (Y ω) univ = eVariationOn (fun s => X s ω) (Iic t) := by
    have h := eVariationOn.comp_eq_of_monotoneOn (t := univ) (fun s => X s ω)
      (Subtype.val : Iic t → ι) (fun _ _ _ _ h => h)
    simpa only [Y,ContinuousMap.coe_mk,Function.comp_def,image_univ,Subtype.range_coe_subtype,
      setOf_mem_eq] using h
  exact ENNReal.measurable_toReal.comp (by simpa only [Function.comp_def,he] using hv)

/-- The continuous version of the variation process is the actual supremum
 variation on [bottom,t], not an externally specified process. -/
theorem variation_process_continuous {ι : Type*} [LinearOrder ι] [OrderBot ι]
    [TopologicalSpace ι] [OrderTopology ι]
    (f : ι → ℝ) (hb : BoundedVariationOn f univ) (hc : Continuous f) :
    Continuous (fun t => (eVariationOn f (Iic t)).toReal) := by
  have he (t : ι) : variationOnFromTo f univ ⊥ t = (eVariationOn f (Iic t)).toReal := by
    rw [variationOnFromTo.eq_of_le f univ bot_le,univ_inter,Icc_bot]
  have h : Continuous (variationOnFromTo f univ ⊥) := continuous_iff_continuousAt.mpr fun t =>
    (hb.continuousAt_variationOnFromTo_iff ⊥ t).mpr hc.continuousAt
  convert h using 1
  funext t; exact (he t).symm

end Asakura.FullAudit

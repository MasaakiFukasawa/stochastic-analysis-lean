import FullAuditVariationProcess
import Mathlib.Topology.Order.IntermediateValue

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.FullAudit
open Asakura.Chapter2Written
set_option backward.isDefEq.respectTransparency false

noncomputable def pathVariation {ι : Type*} [LinearOrder ι] (X : ι → ℝ) (t : ι) : ℝ :=
  (eVariationOn X (Iic t)).toReal

noncomputable def variationStop {Ω ι : Type*} [CompleteLinearOrder ι]
    (X : ι → Ω → ℝ) (k : ℝ) (ω : Ω) : ι :=
  sInf {t | k ≤ pathVariation (fun s => X s ω) t}

theorem path_variation_mono {ι : Type*} [LinearOrder ι] (f : ι → ℝ)
    (hb : BoundedVariationOn f univ) : Monotone (pathVariation f) := by
  intro s t hst
  exact ENNReal.toReal_mono (hb.mono (subset_univ _))
    (eVariationOn.mono f (Iic_subset_Iic.mpr hst))

theorem path_variation_initial {ι : Type*} [LinearOrder ι] [OrderBot ι] (f : ι → ℝ) :
    pathVariation f ⊥ = 0 := by
  simp [pathVariation,eVariationOn.subsingleton]

/-- Stopping at total variation is a genuine stopping time in the manuscript's
 filtration, even though the original variation decomposition need not be continuous. -/
theorem variation_stop_stopping {Ω : Type*} {T : EReal} [Fact (0 ≤ T)]
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F)
    (X : ClosedTime T → Ω → ℝ) (hm : ∀ t, Measurable[F t] (X t))
    (hc : ∀ ω, Continuous (fun t => X t ω))
    (hb : ∀ ω, BoundedVariationOn (fun t => X t ω) univ) (k : ℝ) :
    ∀ t, MeasurableSet[F t] {ω | variationStop X k ω ≤ t} := by
  exact closed_hitting_stopping_compact F hF (fun t ω => pathVariation (fun s => X s ω) t)
    (variation_process_adapted F hF X hm hc)
    (fun ω => variation_process_continuous _ (hb ω) (hc ω)) (Ici k) isClosed_Ici

/-- Continuity excludes overshoot. The intermediate value theorem also handles
 the case in which the threshold is never reached before the terminal point. -/
theorem variation_stop_bound {Ω : Type*} {T : EReal} [Fact (0 ≤ T)]
    (X : ClosedTime T → Ω → ℝ) (hc : ∀ ω, Continuous (fun t => X t ω))
    (hb : ∀ ω, BoundedVariationOn (fun t => X t ω) univ) {k : ℝ} (hk : 0 ≤ k) (ω : Ω) :
    pathVariation (fun s => X s ω) (variationStop X k ω) ≤ k := by
  let V := pathVariation (fun s => X s ω)
  have hVm := path_variation_mono _ (hb ω)
  have hVc := variation_process_continuous _ (hb ω) (hc ω)
  by_cases htop : V ⊤ ≤ k
  · exact (hVm le_top).trans htop
  have h0 : V ⊥ = 0 := path_variation_initial _
  obtain ⟨t,ht,hvt⟩ := intermediate_value_Icc (show (⊥ : ClosedTime T) ≤ ⊤ from bot_le)
    hVc.continuousOn (show k ∈ Icc (V ⊥) (V ⊤) from ⟨by simpa only [h0] using hk,(not_le.mp htop).le⟩)
  change V t = k at hvt
  have hτ : variationStop X k ω ≤ t := sInf_le (show t ∈ {t | k ≤ V t} by simp [hvt])
  exact (hVm hτ).trans_eq hvt

/-- Each path is eventually unaffected, using its finite total variation. -/
theorem variation_stop_eventually_terminal {Ω : Type*} {T : EReal} [Fact (0 ≤ T)]
    (X : ClosedTime T → Ω → ℝ)
    (hb : ∀ ω, BoundedVariationOn (fun t => X t ω) univ) (ω : Ω) :
    ∀ᶠ k : ℕ in atTop, variationStop X (k:ℝ) ω = ⊤ := by
  obtain ⟨K,hK⟩ := exists_nat_gt (pathVariation (fun s => X s ω) ⊤)
  filter_upwards [eventually_ge_atTop K] with k hk
  have hlt : pathVariation (fun s => X s ω) ⊤ < (k:ℝ) := hK.trans_le (by exact_mod_cast hk)
  have he : {t | (k:ℝ) ≤ pathVariation (fun s => X s ω) t} = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro t ht
    exact (not_le_of_gt hlt) (ht.trans (path_variation_mono _ (hb ω) le_top))
  simp only [variationStop,he,sInf_empty]

/-- The stopped path's actual total variation is bounded by the stopping level. -/
theorem stopped_path_variation_bound {Ω : Type*} {T : EReal} [Fact (0 ≤ T)]
    (X : ClosedTime T → Ω → ℝ) (hc : ∀ ω, Continuous (fun t => X t ω))
    (hb : ∀ ω, BoundedVariationOn (fun t => X t ω) univ) {k : ℝ} (hk : 0 ≤ k) (ω : Ω) :
    eVariationOn (fun t => X (min t (variationStop X k ω)) ω) univ ≤ ENNReal.ofReal k := by
  have hcomp := eVariationOn.comp_le_of_monotoneOn (fun t => X t ω)
    (s := Iic (variationStop X k ω)) (t := univ) (fun t => min t (variationStop X k ω))
    (fun _ _ _ _ h => min_le_min_right _ h) (fun t _ => show min t (variationStop X k ω) ≤ variationStop X k ω from min_le_right _ _)
  apply hcomp.trans
  have h := variation_stop_bound X hc hb hk ω
  exact (ENNReal.le_ofReal_iff_toReal_le (hb ω |>.mono (subset_univ _)) hk).mpr h

end Asakura.FullAudit

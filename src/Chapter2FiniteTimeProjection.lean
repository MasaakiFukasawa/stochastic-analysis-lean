import Chapter2ActualLocalVariation
import FullAuditBoundedKW

open MeasureTheory Set Filter
open scoped Topology ENNReal Classical
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

noncomputable def finitePrefixTime {T : EReal} [Fact (0 ≤ T)]
    (d : ℝ) (hd : 0 ≤ d) (t : ClosedTime T) : Icc (0:ℝ) d :=
  ⟨(min (t:EReal) (d:EReal)).toReal,by
    constructor
    · exact EReal.toReal_nonneg (le_min t.property.1 (by exact_mod_cast hd))
    · simpa only [EReal.toReal_coe] using
        EReal.toReal_le_toReal (min_le_right (t:EReal) (d:EReal))
          (ne_of_gt ((EReal.bot_lt_coe 0).trans_le (le_min t.property.1 (by exact_mod_cast hd))))
          (EReal.coe_ne_top d)⟩

theorem finite_prefix_time_mono {T : EReal} [Fact (0 ≤ T)]
    (d : ℝ) (hd : 0 ≤ d) : Monotone (finitePrefixTime (T := T) d hd) := by
  intro s t hst
  exact EReal.toReal_le_toReal (min_le_min (show (s:EReal) ≤ (t:EReal) from hst) le_rfl)
    (ne_of_gt ((EReal.bot_lt_coe 0).trans_le (le_min s.property.1 (by exact_mod_cast hd))))
    (ne_of_lt ((min_le_right (t:EReal) (d:EReal)).trans_lt (EReal.coe_lt_top d)))

theorem finite_prefix_time_continuous {T : EReal} [Fact (0 ≤ T)]
    (d : ℝ) (hd : 0 ≤ d) : Continuous (finitePrefixTime (T := T) d hd) := by
  unfold finitePrefixTime
  apply Continuous.subtype_mk
  apply continuous_iff_continuousAt.mpr
  intro t
  exact (EReal.tendsto_toReal
    (ne_of_lt ((min_le_right (t:EReal) (d:EReal)).trans_lt (EReal.coe_lt_top d)))
    (ne_of_gt ((EReal.bot_lt_coe 0).trans_le (le_min t.property.1 (by exact_mod_cast hd))))).comp
    (continuous_subtype_val.min continuous_const).continuousAt

theorem finite_prefix_time_clamp {T : EReal} [Fact (0 ≤ T)]
    (d : ℝ) (hd : 0 ≤ d) (hdT : (d:EReal) ≤ T) (t : ClosedTime T) :
    realTimeClamp (finitePrefixTime d hd t).val = min (realTimeClamp d) t := by
  apply Subtype.ext
  rw [real_time_clamp_eq _ (finitePrefixTime d hd t).property.1
    ((EReal.coe_le_coe (finitePrefixTime d hd t).property.2).trans hdT)]
  change ((min (t:EReal) (d:EReal)).toReal:EReal) = min (realTimeClamp d : EReal) (t:EReal)
  rw [EReal.coe_toReal
    (ne_of_lt ((min_le_right (t:EReal) (d:EReal)).trans_lt (EReal.coe_lt_top d)))
    (ne_of_gt ((EReal.bot_lt_coe 0).trans_le (le_min t.property.1 (by exact_mod_cast hd)))),
    real_time_clamp_eq d hd hdT,min_comm]

/-- Lift finite-interval adapted increasing parts to the original time
space, constantly after the finite endpoint. -/
theorem adapted_variation_of_finite_interval_parts
    {Ω : Type*} {T : EReal} [Fact (0 ≤ T)]
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F)
    (d : ℝ) (hd : 0 ≤ d) (hdT : (d:EReal) ≤ T)
    (U V : Ω → ℝ → ℝ)
    (hm : ∀ r : Icc (0:ℝ) d, Measurable[F (realTimeClamp r.val)] (fun ω => U ω r.val) ∧
      Measurable[F (realTimeClamp r.val)] (fun ω => V ω r.val))
    (hmon : ∀ ω, Monotone (U ω) ∧ Monotone (V ω))
    (hr : ∀ ω r, ContinuousWithinAt (U ω) (Ici r) r ∧ ContinuousWithinAt (V ω) (Ici r) r) :
    AdaptedVariationWitness F (fun t ω => U ω (finitePrefixTime d hd t).val-V ω (finitePrefixTime d hd t).val) := by
  let p := fun t : ClosedTime T => (finitePrefixTime d hd t).val
  have hpm : Monotone p := fun s t hst => finite_prefix_time_mono d hd hst
  have hpc : Continuous p := continuous_subtype_val.comp (finite_prefix_time_continuous d hd)
  refine ⟨fun t ω => U ω (p t),fun t ω => V ω (p t),?_,?_,?_,fun _ _ => rfl⟩
  · intro t
    have ht : realTimeClamp (finitePrefixTime d hd t).val ≤ t := by
      rw [finite_prefix_time_clamp d hd hdT]; exact min_le_right _ _
    exact ⟨((hm _).1).mono (hF ht) le_rfl,((hm _).2).mono (hF ht) le_rfl⟩
  · intro ω
    exact ⟨(hmon ω).1.comp hpm,(hmon ω).2.comp hpm⟩
  · intro ω t
    exact ⟨(hr ω (p t)).1.comp hpc.continuousWithinAt (fun s hs => hpm hs),
      (hr ω (p t)).2.comp hpc.continuousWithinAt (fun s hs => hpm hs)⟩

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.adapted_variation_of_finite_interval_parts

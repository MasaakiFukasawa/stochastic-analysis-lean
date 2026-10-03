import Chapter2CountableVariation
import Chapter2WrittenGridStopping

open MeasureTheory Set Filter
open scoped Topology ENNReal Classical
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

theorem grid_time_monotone {T : EReal} (n : ℕ) : Monotone (gridTime (T := T) n) := by
  intro s t hst
  change extendedGrid T n s.val ≤ extendedGrid T n t.val
  by_cases ht : t.val ≤ ((n:ℝ):EReal)
  · have hs : s.val ≤ ((n:ℝ):EReal) := (show s.val ≤ t.val from hst).trans ht
    rw [extendedGrid,extendedGrid,if_pos hs,if_pos ht]
    apply min_le_min_right
    apply EReal.coe_le_coe
    unfold upperDyadic
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply Int.cast_le.mpr
    apply Int.ceil_mono
    exact mul_le_mul_of_nonneg_left
      (EReal.toReal_le_toReal hst (ne_of_gt ((by simp : (⊥:EReal) < 0).trans_le s.property.1))
        (ne_of_lt (ht.trans_lt (EReal.coe_lt_top _)))) (by positivity)
  · have he : extendedGrid T n t.val = T := by simp only [extendedGrid,if_neg ht]
    rw [he]
    exact (extendedGrid_bounds s.property.1 s.property.2 n).2

/-- Adaptedness of total variation for right-continuous paths, proved by
countable right grids; continuity is not added to the manuscript's A. -/
theorem right_continuous_variation_adapted {Ω : Type*} {T : EReal} [Fact (0 ≤ T)]
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F)
    (X : ClosedTime T → Ω → ℝ) (hm : ∀ t, Measurable[F t] (X t))
    (hr : ∀ ω t, ContinuousWithinAt (fun s => X s ω) (Ici t) t)
    (t : ClosedTime T) : Measurable[F t] (fun ω => (eVariationOn (fun s => X s ω) (Iic t)).toReal) := by
  letI : MeasurableSpace Ω := F t
  let q := fun n s => min (gridTime n s) t
  have hq n : MonotoneOn (q n) (Iic t) := ((grid_time_monotone n).min monotone_const).monotoneOn _
  have hqs n : MapsTo (q n) (Iic t) (Iic t) := fun s _ => show min (gridTime n s) t ≤ t from min_le_right _ _
  have hqc n : (q n '' Iic t).Countable := by
    apply (((gridTime_finite_range T n).image (fun s => min s t)).countable).mono
    rintro _ ⟨s,hs,rfl⟩
    exact ⟨gridTime n s,mem_range_self _,rfl⟩
  have he ω : eVariationOn (fun s => X s ω) (Iic t) = ⨆ n, eVariationOn (fun s => X s ω) (q n '' Iic t) := by
    apply variation_eq_iSup_grid _ q hq hqs
    intro s hs
    apply (hr ω s).tendsto.comp
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have ht := (gridTime_tendsto s).min (tendsto_const_nhds : Tendsto (fun _ : ℕ => t) atTop (𝓝 t))
      simpa only [q,min_eq_left (show s ≤ t from hs)] using ht
    · exact .of_forall (fun n => le_min (extendedGrid_bounds s.property.1 s.property.2 n).1 hs)
  have hmeas n := countable_subset_variation_measurable (q n '' Iic t) (hqc n) X
    (fun s hs => (hm s).mono (hF (by
      obtain ⟨r,hr,he⟩ := hs
      rw [← he]
      exact hqs n hr)) le_rfl)
  have hmi : Measurable (fun ω => ⨆ n, eVariationOn (fun s => X s ω) (q n '' Iic t)) :=
    Measurable.iSup hmeas
  exact ENNReal.measurable_toReal.comp (by simpa only [← he] using hmi)

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.right_continuous_variation_adapted

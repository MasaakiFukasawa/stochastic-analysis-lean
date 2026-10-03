import Chapter2StieltjesRestriction

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit
set_option maxHeartbeats 800000

/-- Stopping an increasing function inside its time interval preserves
monotonicity on that interval. -/
theorem stopped_monotone_on_interval (a b c : ℝ) (hac : a ≤ c) (hcb : c ≤ b)
    (A : ℝ → ℝ) (hA : MonotoneOn A (Icc a b)) :
    MonotoneOn (fun r => A (min c r)) (Icc a b) := by
  intro r hr s hs hrs
  apply hA
  · exact ⟨le_min hac hr.1,(min_le_right _ _).trans hr.2⟩
  · exact ⟨le_min hac hs.1,(min_le_right _ _).trans hs.2⟩
  · exact min_le_min_left c hrs

/-- Continuity is retained when stopping at an interior or endpoint time. -/
theorem stopped_continuous_on_interval (a b c : ℝ) (hac : a ≤ c) (hcb : c ≤ b)
    (A : ℝ → ℝ) (hc : ContinuousOn A (Icc a b)) :
    ContinuousOn (fun r => A (min c r)) (Icc a b) := by
  apply hc.comp (continuous_const.min continuous_id).continuousOn
  intro r hr
  exact ⟨le_min hac hr.1,(min_le_right _ _).trans hr.2⟩

/-- Pathwise identification of the stopped Stieltjes measure with a
restriction of the original measure. This is the missing measure identity
behind the localization argument for elementary-integrand density. -/
theorem stopped_stieltjes_measure_restriction
    (a b c : ℝ) (hac : a ≤ c) (hcb : c ≤ b)
    (A : ℝ → ℝ) (hA : MonotoneOn A (Icc a b)) (hc : ContinuousOn A (Icc a b)) :
    let hr := fun x hx => (hc x hx).mono inter_subset_left
    let hAs := stopped_monotone_on_interval a b c hac hcb A hA
    let hcs := stopped_continuous_on_interval a b c hac hcb A hc
    (intervalStieltjes a b (hac.trans hcb) (fun r => A (min c r)) hAs
      (fun x hx => (hcs x hx).mono inter_subset_left)).measure =
      (intervalStieltjes a b (hac.trans hcb) A hA hr).measure.restrict (Iic c) := by
  intro hr hAs hcs
  let hrs : ∀ x, x ∈ Icc a b → ContinuousWithinAt (fun r => A (min c r)) (Icc a b ∩ Ici x) x :=
    fun x hx => (hcs x hx).mono inter_subset_left
  letI := intervalStieltjes_finite a b (hac.trans hcb) A hA hr
  letI := intervalStieltjes_finite a b (hac.trans hcb) (fun r => A (min c r)) hAs hrs
  have hl := interval_stieltjes_left_limit a b (hac.trans hcb) (fun _ : Unit => A)
    (fun _ => hA) (fun _ => hr) ()
  have hls := interval_stieltjes_left_limit a b (hac.trans hcb)
    (fun _ : Unit => fun r => A (min c r)) (fun _ => hAs) (fun _ => hrs) ()
  apply Measure.ext_of_Iic
  intro r
  rw [Measure.restrict_apply measurableSet_Iic,Iic_inter_Iic,
    StieltjesFunction.measure_Iic _ hls,StieltjesFunction.measure_Iic _ hl]
  congr 1
  change A (min c (intervalClamp a b (hac.trans hcb) r))-A (min c a) =
    A (intervalClamp a b (hac.trans hcb) (min r c))-A a
  rw [min_eq_right hac]
  congr 1
  congr 1
  change min c (max a (min b r)) = max a (min b (min r c))
  rw [min_max_distrib_left,min_eq_right hac,← min_assoc,min_eq_left hcb]
  rw [min_left_comm b r c,min_eq_right hcb,min_comm r c]

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.stopped_monotone_on_interval
#print axioms Asakura.Chapter2Complete.stopped_continuous_on_interval
#print axioms Asakura.Chapter2Complete.stopped_stieltjes_measure_restriction

import Chapter4BrownianSystem
import Chapter7ClockHalfTime
import Chapter2LevelLocalization
import Chapter2StoppedRegularity
import Chapter2LocalQuadraticVariation

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter4
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

/-- The capped exit time of x+B from (0,R), constructed by hitting the
closed level R/2 of |x+B-R/2|. Continuity gives no overshoot and identifies
the two boundary values whenever exit precedes the deterministic cap. -/
theorem brownian_capped_exit_stop
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (B : BrownianSystem P 1) (x R c : ℝ) (hx : 0 ≤ x) (hxR : x ≤ R) (hc : 0 ≤ c) :
    ∃ τ : Ω → HalfClosedTime,
      (∀ t,MeasurableSet[B.F t] {w | τ w ≤ t}) ∧
      (∀ w,τ w ≤ realTimeClamp c) ∧
      (∀ᵐ w ∂P,∀ t,x+B.W 0 (min (τ w) t) w ∈ Icc 0 R) ∧
      (∀ᵐ w ∂P,τ w < realTimeClamp c → x+B.W 0 (τ w) w = 0 ∨ x+B.W 0 (τ w) w = R) := by
  have hcap t : MeasurableSet[B.F t] {w : Ω | realTimeClamp c ≤ t} := by
    by_cases h : realTimeClamp c ≤ t <;> simp [h]
  obtain ⟨hBa,hBc⟩ := (B.martingale 0).stopped_regular P B.F B.mono B.le
    (fun _ => realTimeClamp c) hcap (fun _ => changed_time_finite c hc)
  let Y := fun t w => |x+B.W 0 (min (realTimeClamp c) t) w-R/2|
  have hYa t : Measurable[B.F t] (Y t) := measurable_norm.comp ((measurable_const.add (hBa t)).sub_const (R/2))
  have hYc w : Continuous (fun t => Y t w) := ((continuous_const.add (hBc w)).sub continuous_const).norm
  let hit := fun w => sInf {t | R/2 ≤ Y t w}
  have hh t : MeasurableSet[B.F t] {w | hit w ≤ t} :=
    continuous_hitting_stopping_written B.F B.mono Y hYa hYc (Ici (R/2)) isClosed_Ici t
  let τ := fun w => min (hit w) (realTimeClamp c)
  have hτ := (written_stopping_min_max B.F hit (fun _ => realTimeClamp c) hh hcap).1
  have hτc w : τ w ≤ realTimeClamp c := min_le_right _ _
  have hb : ∀ᵐ w ∂P,∀ t,x+B.W 0 (min (τ w) t) w ∈ Icc 0 R := by
    filter_upwards [(B.martingale 0).initial P B.F] with w hw
    intro t
    have h0 : Y ⊥ w ≤ R/2 := by
      dsimp only [Y]
      simp only [min_bot_right,hw,Pi.zero_apply,add_zero]
      exact abs_le.mpr ⟨by linarith,by linarith⟩
    have hbound := continuous_level_stop_bound (fun s => Y s w) (hYc w) (R/2) h0
      (min (τ w) t) ((min_le_left _ _).trans (min_le_left _ _))
    have hm : min (realTimeClamp c) (min (τ w) t) = min (τ w) t :=
      min_eq_right ((min_le_left _ _).trans (hτc w))
    simp only [Y,hm] at hbound
    have h := abs_le.mp hbound
    exact ⟨by linarith [h.1],by linarith [h.2]⟩
  refine ⟨τ,hτ,hτc,hb,?_⟩
  filter_upwards [hb] with w hw
  intro ht
  have hhit : hit w < realTimeClamp c := (min_lt_iff.mp ht).resolve_right (lt_irrefl _)
  have he : τ w = hit w := min_eq_left hhit.le
  obtain ⟨s,hs,hlevel⟩ := (closed_hitting_lower_event (fun t => Y t w) (hYc w)
    (Ici (R/2)) isClosed_Ici (τ w) (lt_trans ht (changed_time_finite c hc))).mp he.ge
  have hts : τ w ≤ s := he ▸ sInf_le hlevel
  have hst : s = τ w := le_antisymm hs hts
  subst s
  have hcτ : min (realTimeClamp c) (τ w) = τ w := min_eq_right (hτc w)
  change R/2 ≤ Y (τ w) w at hlevel
  simp only [Y,hcτ] at hlevel
  have hbτ := hw ⊤
  simp only [min_top_right,mem_Icc] at hbτ
  by_cases h : 0 ≤ x+B.W 0 (τ w) w-R/2
  · rw [abs_of_nonneg h] at hlevel
    right
    linarith [hbτ.2]
  · rw [abs_of_neg (lt_of_not_ge h)] at hlevel
    left
    linarith [hbτ.1]

end Asakura.Chapter7

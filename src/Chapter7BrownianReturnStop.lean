import Chapter7BrownianFutureLevels
import Chapter7OpenClosedHitting

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter4
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

/-- The next return after a waiting period is a genuine stopping time.
The second coordinate records elapsed time after the old stopping time;
thus a closed-set hit enforces both the delay and the return to zero. -/
theorem brownian_delayed_return
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (B : BrownianSystem P 1) (σ : Ω → HalfClosedTime)
    (hσ : ∀ t,MeasurableSet[B.F t] {w | σ w ≤ t})
    (hσfin : ∀ᵐ w ∂P,σ w < ⊤) :
    ∃ τ : Ω → HalfClosedTime,
      (∀ t,MeasurableSet[B.F t] {w | τ w ≤ t}) ∧
      (∀ᵐ w ∂P,τ w < ⊤ ∧ σ w ≤ τ w ∧
        (halfTimeReal (σ w):ℝ)+1 ≤ (halfTimeReal (τ w):ℝ) ∧ B.W 0 (τ w) w = 0) := by
  let Y := fun t w => (B.W 0 t w,(halfTimeReal t:ℝ)-(halfTimeReal (min (σ w) t):ℝ))
  let C : Set (ℝ × ℝ) := {0} ×ˢ Ici 1
  have hC : IsClosed C := isClosed_singleton.prod isClosed_Ici
  have hm t (ht : t < ⊤) : Measurable[B.F t] (Y t) := by
    have hmin := stopped_min_measurable B.F B.mono σ hσ t
    have hreal : Measurable[B.F t] (fun w => (halfTimeReal (min (σ w) t):ℝ)) :=
      measurable_ereal_toReal.comp (measurable_subtype_coe.comp hmin)
    exact ((B.martingale 0).adapted P B.F t ht).prodMk (measurable_const.sub hreal)
  have hc w t (ht : t < ⊤) : ContinuousAt (fun s => Y s w) t := by
    have hmin : ContinuousAt (fun s => (halfTimeReal (min (σ w) s):ℝ)) t :=
      (changed_time_coordinate_continuousAt _ (lt_of_le_of_lt (min_le_right _ _) ht)).comp
        (continuous_const.min continuous_id).continuousAt
    exact ((B.martingale 0).path P B.F w t ht).prodMk
      ((changed_time_coordinate_continuousAt t ht).sub hmin)
  let τ := fun w => sInf {t | t = ⊤ ∨ Y t w ∈ C}
  refine ⟨τ,open_continuous_hitting_stopping B.F B.mono Y hm hc C hC,?_⟩
  filter_upwards [hσfin,brownian_future_levels P B] with w hσw hfuture
  obtain ⟨r,hr,har,hzero⟩ := hfuture ((halfTimeReal (σ w):ℝ)+1) 0
  have hσr : σ w ≤ realTimeClamp r := by
    obtain ⟨s,hs,_,he⟩ := finite_closed_time_real (σ w) hσw
    rw [← he,changed_time_real s hs] at har
    rw [← he]
    exact real_time_clamp_mono (by linarith : s ≤ r)
  have hmem : Y (realTimeClamp r) w ∈ C := by
    change B.W 0 (realTimeClamp r) w = 0 ∧ 1 ≤ (halfTimeReal (realTimeClamp r):ℝ)-(halfTimeReal (min (σ w) (realTimeClamp r)):ℝ)
    rw [changed_time_real r hr,min_eq_left hσr]
    exact ⟨hzero,by linarith⟩
  have hτr : τ w ≤ realTimeClamp r := sInf_le (show realTimeClamp r ∈ {t | t = ⊤ ∨ Y t w ∈ C} from Or.inr hmem)
  have hτfin : τ w < ⊤ := lt_of_le_of_lt hτr (changed_time_finite r hr)
  have hattain := (open_hitting_set_closed (fun t => Y t w) (hc w) C hC).sInf_mem
    (show ({t | t = ⊤ ∨ Y t w ∈ C}).Nonempty from ⟨⊤,Or.inl rfl⟩)
  have hval : Y (τ w) w ∈ C := hattain.resolve_left (ne_of_lt hτfin)
  change B.W 0 (τ w) w = 0 ∧ 1 ≤ (halfTimeReal (τ w):ℝ)-(halfTimeReal (min (σ w) (τ w)):ℝ) at hval
  have hστ : σ w ≤ τ w := by
    by_contra h
    have he : min (σ w) (τ w) = τ w := min_eq_right (le_of_not_ge h)
    rw [he,sub_self] at hval
    linarith [hval.2]
  rw [min_eq_left hστ] at hval
  exact ⟨hτfin,hστ,by linarith [hval.2],hval.1⟩

end Asakura.Chapter7

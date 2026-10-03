import Chapter6ContinuousCoefficientRegular
import Chapter4MomentLevelStops

open MeasureTheory Set Filter
open scoped Topology BigOperators
namespace Asakura.Chapter6
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter7
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false

/-- Actual exit times on a fixed finite horizon. Bounds are almost sure,
so the Brownian initial value need only equal zero almost surely. -/
theorem brownian_norm_level_stops {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (R : ℝ) (hR : 0≤R) :
    ∃ τ : ℕ → Ω → HalfClosedTime,
      (∀ n t,MeasurableSet[B.F t] {w | τ n w≤t}) ∧
      (∀ n w,τ n w≤realTimeClamp R) ∧
      (∀ w,∀ᶠ n in atTop,τ n w=realTimeClamp R) ∧
      ∀ᵐ w ∂P,∀ n (r : ℝ),0≤r → realTimeClamp r≤τ n w →
        ‖WithLp.toLp 2 (fun j => B.W j (realTimeClamp r) w)‖≤(n:ℝ)+1 := by
  let U := fun t w => ‖WithLp.toLp 2 (fun j => B.W j (min (realTimeClamp R) t) w)‖
  have hRt : (realTimeClamp R : HalfClosedTime)<⊤ := changed_time_finite R hR
  have hUc w : Continuous (fun t => U t w) := by
    apply Continuous.norm
    apply (PiLp.continuousLinearEquiv 2 ℝ (fun _:Fin d => ℝ)).symm.continuous.comp
    exact continuous_pi (fun j => open_path_stopped_continuous (B.W j) ((B.martingale j).path P B.F) R hR (EReal.coe_lt_top _) w)
  have hUa t : Measurable[B.F t] (U t) := by
    letI : MeasurableSpace Ω := B.F t
    apply Measurable.norm
    apply (PiLp.continuousLinearEquiv 2 ℝ (fun _:Fin d => ℝ)).symm.continuous.measurable.comp
    exact measurable_pi_iff.mpr (fun j => ((B.martingale j).adapted P B.F _ ((min_le_left _ _).trans_lt hRt)).mono (B.mono (min_le_right _ _)) le_rfl)
  let hit := fun (n : ℕ) w => sInf {t | (n:ℝ)+1≤U t w}
  let τ := fun n w => min (hit n w) (realTimeClamp R)
  have hh n := continuous_hitting_stopping_written B.F B.mono U hUa hUc (Ici ((n:ℝ)+1)) isClosed_Ici
  refine ⟨τ,?_,fun _ _ => min_le_right _ _,?_,?_⟩
  · intro n
    exact (written_stopping_min_max B.F (hit n) (fun _ => realTimeClamp R) (hh n)
      (fun t => by by_cases h : (realTimeClamp R : HalfClosedTime)≤t <;> simp [h])).1
  · intro w
    let f : C(HalfClosedTime,ℝ) := ⟨fun t => U t w,hUc w⟩
    obtain ⟨k,hk⟩ := exists_nat_gt ‖f‖
    filter_upwards [eventually_ge_atTop k] with n hn
    have hkn : (k:ℝ)≤n := by exact_mod_cast hn
    have hempty : {t | (n:ℝ)+1≤U t w}=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro t ht
      change (n:ℝ)+1≤U t w at ht
      have hb := f.norm_coe_le_norm t
      change |U t w|≤‖f‖ at hb
      linarith [le_abs_self (U t w)]
    simp only [τ,hit,hempty,sInf_empty,min_top_left]
  · filter_upwards [ae_all_iff.mpr (fun j => (B.martingale j).initial P B.F)] with w hw
    have hU0 : U ⊥ w=0 := by simp [U,hw]; rfl
    intro n r hr hrt
    have hbefore : realTimeClamp r≤hit n w := hrt.trans (min_le_left _ _)
    have hb := continuous_level_stop_bound (fun t => U t w) (hUc w) ((n:ℝ)+1)
      (by rw [hU0]; positivity) (realTimeClamp r) hbefore
    have hrR : realTimeClamp r≤(realTimeClamp R : HalfClosedTime) := hrt.trans (min_le_right _ _)
    simpa only [U,min_eq_right hrR] using hb

end Asakura.Chapter6

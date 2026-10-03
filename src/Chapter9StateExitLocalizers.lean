import Chapter2ContinuousLocalizers
import Chapter9FiniteIntervalMartingale

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter9
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

/-- Exit from expanding state balls, capped by a deterministic exhaustion.
 The initial state need not be bounded or zero. -/
theorem continuous_state_exit_localizers {Ω E : Type*} [m : MeasurableSpace Ω]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    (F : HalfClosedTime → MeasurableSpace Ω) (hF : Monotone F)
    (Z : HalfClosedTime → Ω → E)
    (hm : ∀ t,Measurable[F t] (Z t)) (hc : ∀ w,Continuous (fun t => Z t w)) :
    ∃ τ : ℕ → Ω → HalfClosedTime,
      (∀ n t,MeasurableSet[F t] {w | τ n w≤t}) ∧
      (∀ w,Monotone (fun n => τ n w)) ∧ (∀ n w,τ n w<⊤) ∧
      (∀ w t,t<⊤ → ∃ n,t<τ n w) ∧
      (∀ (n : ℕ) w,‖Z ⊥ w‖>(n:ℝ) → τ n w=⊥) ∧
      (∀ (n : ℕ) w,‖Z ⊥ w‖≤(n:ℝ) → ∀ t≤τ n w,‖Z t w‖≤(n:ℝ)) := by
  obtain ⟨u,hu,hut,huc⟩ := deterministic_time_exhaustion (T := (⊤:EReal)) (by simp)
  let hit := fun (n : ℕ) w => sInf {t | (n:ℝ)≤‖Z t w‖}
  let τ := fun n w => min (hit n w) (u n)
  have hhit n : ∀ t,MeasurableSet[F t] {w | hit n w≤t} :=
    continuous_hitting_stopping_written F hF (fun t w => ‖Z t w‖)
      (fun t => by
        letI : MeasurableSpace Ω := F t
        exact (hm t).norm) (fun w => (hc w).norm) (Ici (n:ℝ)) isClosed_Ici
  have hτ n : ∀ t,MeasurableSet[F t] {w | τ n w≤t} :=
    (written_stopping_min_max F (hit n) (fun _ => u n) (hhit n)
      (fun t => by by_cases h : u n≤t <;> simp [h])).1
  have hmono w : Monotone (fun n => τ n w) := by
    intro n k hnk
    apply min_le_min _ (hu hnk)
    apply sInf_le_sInf
    intro t ht
    exact (show (n:ℝ)≤k by exact_mod_cast hnk).trans ht
  have htop n w : τ n w<⊤ := (min_le_right _ _).trans_lt (hut n)
  refine ⟨τ,hτ,hmono,htop,?_,?_,?_⟩
  · intro w t ht
    obtain ⟨j,hj⟩ := huc t ht
    let f : C(HalfClosedTime,ℝ) := ⟨fun r => ‖Z r w‖,(hc w).norm⟩
    obtain ⟨k,hk⟩ := exists_nat_gt ‖f‖
    let n := max j k
    have htU : t<u n := hj.trans_le (hu (le_max_left _ _))
    have hthit : t<hit n w := by
      by_contra hh
      obtain ⟨r,hr,hlevel⟩ := (closed_hitting_lower_event (fun r => ‖Z r w‖)
        (hc w).norm (Ici (n:ℝ)) isClosed_Ici t ht).mp (le_of_not_gt hh)
      have hf : ‖Z r w‖≤‖f‖ := by
        simpa only [f,ContinuousMap.coe_mk,norm_norm] using f.norm_coe_le_norm r
      have hkn : (k:ℝ)≤n := by exact_mod_cast le_max_right j k
      exact (not_le_of_gt (hk.trans_le hkn)) (hlevel.trans hf)
    exact ⟨n,lt_min hthit htU⟩
  · intro n w hw
    have hh : hit n w≤⊥ := sInf_le hw.le
    exact bot_unique ((min_le_left _ _).trans hh)
  · intro n w hw t ht
    exact continuous_level_stop_bound (fun r => ‖Z r w‖) (hc w).norm (n:ℝ) hw t
      (ht.trans (min_le_left _ _))
end Asakura.Chapter9

import Chapter4MomentLevelStops
import Chapter4VectorFiniteLift

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter4.Vector
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false

/-- Construct the level stops and their Lp random continuous paths. No
moment assumption is made on the unstopped path. -/
theorem finite_path_moment_stops
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsFiniteMeasure P]
    {T : EReal} [Fact (0≤T)]
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (R : ℝ) (hR : 0≤R) (hRT : (R:EReal)<T)
    {dim : ℕ} (Y : Ω → C(Icc (0:ℝ) R,Fin dim → ℝ))
    (ha : ∀ r,Measurable[F (realTimeClamp r.val)] (fun w => Y w r))
    (p : ℝ≥0∞) (hi0 : MemLp (fun w => Y w (finitePrefixTime (T := T) R hR ⊥)) p P) :
    ∃ (τ : ℕ → Ω → ClosedTime T) (Z : ℕ → Ω → C(Icc (0:ℝ) R,Fin dim → ℝ)),
      (∀ n t,MeasurableSet[F t] {w | τ n w≤t}) ∧
      (∀ w,Monotone (fun n => τ n w)) ∧ (∀ n w,τ n w<⊤) ∧
      (∀ n w,τ n w≤realTimeClamp R) ∧
      (∀ n,Measurable[m] (Z n)) ∧ (∀ n,MemLp (Z n) p P) ∧
      (∀ n r,Measurable[F (realTimeClamp r.val)] (fun w => Z n w r)) ∧
      (∀ n w r,Z n w r=Y w (finitePrefixTime (T := T) R hR (min (τ n w) (realTimeClamp r.val)))) ∧
      (∀ w,∀ᶠ n in atTop,Z n w=Y w) := by
  classical
  letI : MeasurableSpace Ω := m
  let U := fun t w => Y w (finitePrefixTime (T := T) R hR t)
  have hU := finite_path_lift_regular F hF R hR hRT.le Y ha
  let hit := fun (n : ℕ) w => sInf {t | (n:ℝ)≤‖U t w‖}
  let τ := fun n w => min (hit n w) (realTimeClamp (T := T) R)
  have hh (n : ℕ) := continuous_hitting_stopping_written F hF (fun t w => ‖U t w‖)
    (fun t => by
      letI : MeasurableSpace Ω := F t
      exact (hU.1 t).norm) (fun w => (hU.2 w).norm) (Ici (n:ℝ)) isClosed_Ici
  have hτ n : ∀ t,MeasurableSet[F t] {w | τ n w≤t} :=
    (written_stopping_min_max F (hit n) (fun _ => realTimeClamp R) (hh n)
      (fun t => by by_cases h : realTimeClamp (T := T) R≤t <;> simp [h])).1
  have hτc n w : Continuous (fun r : Icc (0:ℝ) R => U (min (τ n w) (realTimeClamp r.val)) w) :=
    (hU.2 w).comp (continuous_const.min (real_time_clamp_continuous.comp continuous_subtype_val))
  let Z := fun n w => (⟨fun r => U (min (τ n w) (realTimeClamp r.val)) w,hτc n w⟩ : C(Icc (0:ℝ) R,Fin dim → ℝ))
  have hZa n r : Measurable[F (realTimeClamp r.val)] (fun w => Z n w r) := by
    letI : MeasurableSpace Ω := F (realTimeClamp r.val)
    apply measurable_pi_iff.mpr
    intro i
    exact stopped_min_value_measurable F hF (τ n) (hτ n) (fun t w => U t w i)
      (fun t => (measurable_pi_apply i).comp (hU.1 t))
      (fun w t => ((continuous_apply i).comp (hU.2 w)).continuousAt.continuousWithinAt) _
  have hZm n : Measurable[m] (Z n) := ContinuousMap.measurable_iff_eval.mpr (fun r => (hZa n r).mono (hle _) le_rfl)
  have hbound n w : ‖Z n w‖≤‖U ⊥ w‖+(n:ℝ) := by
    apply (ContinuousMap.norm_le _ (add_nonneg (norm_nonneg _) (Nat.cast_nonneg n))).2
    intro r
    have hb := continuous_level_stop_bound_with_initial (fun t => ‖U t w‖) (hU.2 w).norm (n:ℝ)
      (min (realTimeClamp R) (realTimeClamp r.val))
    simp only [abs_norm] at hb
    change ‖U (min (τ n w) (realTimeClamp r.val)) w‖≤_
    dsimp only [τ,hit]
    rw [min_assoc]
    exact hb.trans (max_le (le_add_of_nonneg_right (Nat.cast_nonneg n)) (le_add_of_nonneg_left (norm_nonneg _)))
  have hZi n := stopped_path_memLp_of_initial_bound P (Z n) (hZm n).aestronglyMeasurable
    (fun w => ‖U ⊥ w‖) p hi0.norm (n:ℝ) (Nat.cast_nonneg n) (.of_forall (fun w => by simpa only [abs_norm] using hbound n w))
  refine ⟨τ,Z,hτ,?_,?_,(fun _ _ => min_le_right _ _),hZm,hZi,hZa,fun _ _ _ => rfl,?_⟩
  · intro w n k hnk
    apply min_le_min _ le_rfl
    apply sInf_le_sInf
    intro t ht
    exact (show (n:ℝ)≤k by exact_mod_cast hnk).trans ht
  · intro n w
    exact (min_le_right _ _).trans_lt (real_time_below R hR hRT)
  · intro w
    obtain ⟨k,hk⟩ := exists_nat_gt ‖Y w‖
    filter_upwards [eventually_ge_atTop k] with n hn
    have hkn : (k:ℝ)≤n := by exact_mod_cast hn
    have hempty : {t | (n:ℝ)≤‖U t w‖}=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro t ht
      exact (not_le_of_gt (hk.trans_le hkn)) (ht.trans (ContinuousMap.norm_coe_le_norm (Y w) _))
    have hhit : hit n w=⊤ := by simp only [hit,hempty,sInf_empty]
    apply ContinuousMap.ext
    intro r
    change U (min (min (hit n w) (realTimeClamp R)) (realTimeClamp r.val)) w=Y w r
    rw [min_assoc,min_eq_right (real_time_clamp_mono r.property.2)]
    rw [hhit,min_top_left]
    simpa only [U,projIcc_of_mem hR r.property] using finite_path_lift_real R hR hRT.le Y w r.val r.property

end Asakura.Chapter4.Vector

import Chapter7ClosedLocalBound
import Chapter2LevelLocalization
import Chapter2LocalQuadraticVariation
import Chapter2StoppedRegularity

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

/-- Continuity at the endpoint gives level localizers that eventually equal
the endpoint on every path, and stopped martingales valid at that endpoint. -/
theorem closed_local_level_localizers
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t,F t ≤ m)
    (X : ClosedTime T → Ω → ℝ) (hX : LocalMProcessWitness P F X)
    (ha : ∀ t,Measurable[F t] (X t)) (hc : ∀ w,Continuous (fun t => X t w)) :
    ∃ τ : ℕ → Ω → ClosedTime T,
      (∀ n t,MeasurableSet[F t] {w | τ n w ≤ t}) ∧
      (∀ w,Monotone (fun n => τ n w)) ∧
      (∀ w,∃ n,τ n w = ⊤) ∧
      (∀ n,ContinuousM2Witness P F (fun t w => X (min (τ n w) t) w)) := by
  let τ := fun (n : ℕ) w => sInf {t | (n:ℝ) ≤ |X t w|}
  have ht n : ∀ t,MeasurableSet[F t] {w | τ n w ≤ t} :=
    continuous_hitting_stopping_written F hF (fun t w => |X t w|)
      (fun t => by
        letI : MeasurableSpace Ω := F t
        simpa only [Real.norm_eq_abs] using (ha t).norm)
      (fun w => (hc w).abs) (Ici (n:ℝ)) isClosed_Ici
  have hm w : Monotone (fun n => τ n w) := by
    intro n k hnk
    apply sInf_le_sInf
    intro t ht
    exact (show (n:ℝ) ≤ k by exact_mod_cast hnk).trans ht
  refine ⟨τ,ht,hm,?_,?_⟩
  · intro w
    let f : C(ClosedTime T,ℝ) := ⟨fun t => X t w,hc w⟩
    obtain ⟨n,hn⟩ := exists_nat_gt ‖f‖
    refine ⟨n,?_⟩
    have he : {t | (n:ℝ) ≤ |X t w|} = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro t ht
      have hb : |X t w| ≤ ‖f‖ := by simpa only [f,ContinuousMap.coe_mk,Real.norm_eq_abs] using f.norm_coe_le_norm t
      exact (not_le_of_gt hn) (ht.trans hb)
    simp only [τ,he,sInf_empty]
  · intro n
    apply closed_local_martingale_of_path_bound P F hle _ (hX.stopped P F hF hle (τ n) (ht n))
      (stopped_min_value_measurable F hF (τ n) (ht n) X ha (fun w t => (hc w).continuousAt.continuousWithinAt))
      (fun w => (hc w).comp (continuous_const.min continuous_id)) (fun _ => (n:ℝ)) (memLp_const _)
    filter_upwards [hX.initial P F] with w hw
    intro t
    rw [Real.norm_eq_abs]
    apply continuous_level_stop_bound (fun s => |X s w|) (hc w).abs (n:ℝ)
    · simpa only [hw,Pi.zero_apply,abs_zero] using Nat.cast_nonneg (α := ℝ) n
    · exact min_le_left _ _

end Asakura.Chapter7

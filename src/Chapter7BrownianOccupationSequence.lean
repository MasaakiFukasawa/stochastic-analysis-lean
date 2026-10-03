import Chapter7AugmentedMartingale
import Chapter7StrongMarkovStay
import Chapter7StayEventAtNextStop
import Chapter7InfiniteIntervalOccupation

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

/-- All probabilistic steps of infinite occupation, once the actual return
sequence is supplied: strong Markov, maximal inequality, measurability at
the next return, iteration of conditional failures, and disjoint lengths. -/
theorem brownian_occupation_of_returns
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (hB : IsPreBrownianReal B P)
    (hm : ∀ t,Measurable (B t)) (hc : ∀ w,Continuous (fun t => B t w))
    (τ : ℕ → Ω → ℝ≥0)
    (hτ : ∀ n t,MeasurableSet[Asakura.nullAugmentation P (pastSigma B t)] {w | τ n w ≤ t})
    (hreturn : ∀ᵐ w ∂P,∀ n,τ n w+1 ≤ τ (n+1) w ∧ B (τ n w) w = 0) :
    ∀ᵐ w ∂P,volume {t : ℝ | 0 ≤ t ∧ |B t.toNNReal w| ≤ 1} = ∞ := by
  let F := fun t => Asakura.nullAugmentation (m := m) P (pastSigma B t)
  have hF : Monotone F := fun s t hst => null_augmentation_mono P (past_sigma_mono B hst)
  have hl t : F t ≤ m := fun _ he => he.1
  have hn t N hmN hzN : MeasurableSet[F t] N := null_augmentation_null P (pastSigma B t) N hmN hzN
  let G := fun n => writtenStoppedSpace m F (τ n) (hτ n)
  have hG : Monotone G := by
    apply monotone_nat_of_le_succ
    intro n
    apply stopped_space_mono_ae P F hl hn _ _ (hτ n) (hτ (n+1))
    exact hreturn.mono fun w hw => (le_add_right le_rfl).trans (hw n).1
  let δ : ℝ≥0 := 1/8
  let A := fun n => {w | ∀ r : ℝ≥0,r ≤ δ → |B (τ n w+r) w-B (τ n w) w| ≤ 1}
  have hAm n : MeasurableSet[G (n+1)] (A n) := by
    apply stay_event_at_next_stop P F hF hl hn B (natural_augmented_adapted P B hm) hc
      (τ n) (τ (n+1)) (hτ n) (hτ (n+1)) δ
    filter_upwards [hreturn] with w hw
    exact (add_le_add le_rfl (show δ ≤ 1 by change (δ:ℝ) ≤ (1:ℝ); norm_num [δ])).trans (hw n).1
  have hcut n E (hE : MeasurableSet[G n] E) : P (E ∩ (A n)ᶜ) ≤ ENNReal.ofReal (δ:ℝ)*P E :=
    strong_markov_stay_failure P B hB hm hc (τ n) (hτ n) δ E hE
  have hi := repeated_events_infinitely_often P G hG A hAm (ENNReal.ofReal (δ:ℝ))
    (by norm_num [δ]) hcut
  filter_upwards [hi,hreturn] with w hw hret
  let J := {n | w ∈ A n}
  have hJ : J.Infinite := Set.infinite_of_forall_exists_gt fun n => by
    obtain ⟨j,hj,hmem⟩ := hw (n+1)
    exact ⟨j,hmem,by omega⟩
  apply infinite_interval_occupation (fun n => (τ n w:ℝ)) (δ:ℝ) (by norm_num [δ])
    (fun n => by
      have hg : (τ n w:ℝ)+1 ≤ (τ (n+1) w:ℝ) := (hret n).1
      have hd : (δ:ℝ) ≤ 1 := by norm_num [δ]
      linarith) J hJ
  intro n hn t ht
  have ht0 : 0 ≤ t := (τ n w).property.trans ht.1.le
  let r := (t-(τ n w:ℝ)).toNNReal
  have hr0 : 0 ≤ t-(τ n w:ℝ) := sub_nonneg.mpr ht.1.le
  have hre : (r:ℝ) = t-(τ n w:ℝ) := Real.coe_toNNReal _ hr0
  have hrδ : r ≤ δ := by change (r:ℝ) ≤ (δ:ℝ); rw [hre]; linarith [ht.2]
  have he : τ n w+r = t.toNNReal := by
    apply Subtype.ext
    change (τ n w:ℝ)+(r:ℝ) = (t.toNNReal:ℝ)
    rw [hre,Real.coe_toNNReal _ ht0]
    ring
  have hv := hn r hrδ
  rw [(hret n).2,sub_zero,he] at hv
  exact ⟨ht0,hv⟩

end Asakura.Chapter7

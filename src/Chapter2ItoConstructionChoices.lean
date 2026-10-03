import Chapter2LocalPathEncoding
import Chapter2CovarianceContinuity
import Chapter2RegularCovarianceChoice
import Chapter2ItoCovarianceCharacterization
import Chapter2TimeExhaustion

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

theorem LocalVariationWitness.congr_before_terminal
    {Ω : Type*} {T : EReal} [Fact (0 ≤ T)]
    (F : ClosedTime T → MeasurableSpace Ω) {A B : ClosedTime T → Ω → ℝ}
    (hA : LocalVariationWitness F A) (he : ∀ t, t < ⊤ → A t = B t) : LocalVariationWitness F B := by
  obtain ⟨τ,ht,hm,htt,hc,hv⟩ := hA.localizers
  refine ⟨τ,ht,hm,htt,hc,?_⟩
  intro n ω
  obtain ⟨U,V,hU,hV,hEq⟩ := hv n ω
  refine ⟨U,V,hU,hV,?_⟩
  intro t
  rw [← congrFun (he _ ((min_le_left _ _).trans_lt (htt n ω))) ω]
  exact hEq t

theorem LocalCovarianceWitness.congr_values_before_terminal
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    {X Y A B : ClosedTime T → Ω → ℝ} (hA : LocalCovarianceWitness P F X Y A)
    (he : ∀ t, t < ⊤ → A t = B t) : LocalCovarianceWitness P F X Y B := by
  refine ⟨hA.defect.congr_before_terminal P F ?_,hA.variation.congr_before_terminal F he⟩
  intro t ht
  rw [he t ht]

/-- A measurable real-time encoding can always be chosen for quadratic
variation. Measurability of the unused value at T is not an extra assumption. -/
theorem quadratic_variation_measurable_encoding
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X : ClosedTime T → Ω → ℝ) (hX : LocalMProcessWitness P F X) :
    ∃ A : ClosedTime T → Ω → ℝ, LocalCovarianceWitness P F X X A ∧
      (∀ ω, MonotoneOn (fun t => A t ω) (Iio ⊤)) ∧
      (∀ ω t, t < ⊤ → ContinuousAt (fun s => A s ω) t) ∧
      (∀ ω, A ⊥ ω = 0) ∧ (∀ r, Measurable[m] (fun ω => A (realTimeClamp r) ω)) := by
  classical
  obtain ⟨A,hA,hm,hc,h0⟩ := local_quadratic_variation_regular_choice P F hF hle hnull X hX
  let B := fun t ω => if t < ⊤ then A t ω else 0
  have he t (ht : t < ⊤) : A t = B t := by funext ω; simp only [B,if_pos ht]
  have hB := hA.congr_values_before_terminal P F he
  refine ⟨B,hB,?_,?_,?_,?_⟩
  · intro ω s hs t ht hst
    change B s ω ≤ B t ω
    rw [← congrFun (he s hs) ω,← congrFun (he t ht) ω]
    exact hm ω hs ht hst
  · intro ω t ht
    exact (hc ω t ht).congr_of_eventuallyEq (by
      filter_upwards [gt_mem_nhds ht] with s hs
      exact (congrFun (he s hs) ω).symm)
  · intro ω
    rw [← congrFun (he ⊥ hT) ω]
    exact h0 ω
  · intro r
    by_cases hr : realTimeClamp (T := T) r < ⊤
    · change Measurable[m] (B (realTimeClamp r))
      rw [← he _ hr]
      exact (hA.adapted P F hX hX _ hr).mono (hle _) le_rfl
    · simp only [B,if_neg hr]
      exact measurable_const

/-- The positive real-valued time exhaustion used throughout the integral
construction exists for every finite or infinite T > 0. -/
theorem positive_real_time_exhaustion
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T) :
    ∃ c : ℕ → ℝ, (∀ n, 0 < c n) ∧ StrictMono c ∧ (∀ n, (c n:EReal) < T) ∧
      StrictMono (fun n => realTimeClamp (T := T) (c n)) ∧
      (∀ n, realTimeClamp (T := T) (c n) < ⊤) ∧
      ∀ t, t < ⊤ → ∃ n, t < realTimeClamp (T := T) (c n) := by
  obtain ⟨u,hu,hm,ht⟩ := exists_seq_strictMono_tendsto' (show (⊥ : ClosedTime T) < ⊤ from hT)
  choose c hc hcT he using fun n => finite_closed_time_real (u n) (hm n).2
  have hce n : (c n:EReal) = (u n:EReal) := by
    have hh := congrArg Subtype.val (he n)
    rw [real_time_clamp_eq _ (hc n) (hcT n).le] at hh
    exact hh
  have hcp n : 0 < c n := by
    apply EReal.coe_lt_coe_iff.mp
    rw [hce]
    exact (hm n).1
  have hcm : StrictMono c := by
    intro i j hij
    apply EReal.coe_lt_coe_iff.mp
    rw [hce,hce]
    exact hu hij
  refine ⟨c,hcp,hcm,hcT,?_,?_,?_⟩
  · simpa only [he] using hu
  · intro n
    rw [he]
    exact (hm n).2
  · intro t ht'
    obtain ⟨n,hn⟩ := (ht.eventually (lt_mem_nhds ht')).exists
    exact ⟨n,by rw [he]; exact hn⟩

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.quadratic_variation_measurable_encoding
#print axioms Asakura.Chapter2Complete.positive_real_time_exhaustion

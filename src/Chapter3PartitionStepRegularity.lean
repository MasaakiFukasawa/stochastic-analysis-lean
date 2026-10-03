import Chapter3PartitionStepPaths
import Chapter3ContinuousAdaptedWeights

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

/-- The constructed countable step process is left continuous at every
finite time. Repeated partition times are allowed. -/
theorem partition_step_left_continuous
    {ι : Type*} [LinearOrder ι] [BoundedOrder ι] [TopologicalSpace ι] [OrderTopology ι]
    (H : ι → ℝ) (τ : ℕ → ι) (hτ : Monotone τ) (h0 : τ 0 = ⊥)
    (hco : ∀ t, t < ⊤ → ∃ N, t < τ N)
    (t : ι) (htt : t < ⊤) : ContinuousWithinAt (partitionStep H τ) (Iic t) t := by
  by_cases ht0 : t = ⊥
  · subst t
    apply (continuousWithinAt_const : ContinuousWithinAt (fun _ : ι => partitionStep H τ ⊥) (Iic ⊥) ⊥).congr_of_eventuallyEq
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact congrArg (partitionStep H τ) (le_bot_iff.mp hs)
    · rfl
  · obtain ⟨j,hj⟩ := partition_interval_index τ h0 hco t (bot_lt_iff_ne_bot.mpr ht0) htt
    apply (continuousWithinAt_const : ContinuousWithinAt (fun _ : ι => H (τ j)) (Iic t) t).congr_of_eventuallyEq
    · filter_upwards [self_mem_nhdsWithin,nhdsWithin_le_nhds (Ioi_mem_nhds hj.1)] with s hs hsj
      exact partition_step_value H τ hτ s j ⟨hsj,hs.trans hj.2⟩
    · exact partition_step_value H τ hτ t j hj

/-- Strict stopping events are measurable in the current sigma algebra,
using the already constructed measurable stopped time. -/
theorem strict_stopping_event_measurable
    {Ω : Type*} {T : EReal} [Fact (0 ≤ T)]
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F)
    (σ : Ω → ClosedTime T) (hσ : ∀ t, MeasurableSet[F t] {ω | σ ω ≤ t})
    (t : ClosedTime T) : MeasurableSet[F t] {ω | σ ω < t} := by
  have h := (stopped_min_measurable F hF σ hσ t) (measurableSet_Iio (a := t))
  convert h using 1
  ext ω
  simp only [mem_setOf_eq,mem_preimage,mem_Iio,min_lt_iff,lt_self_iff_false,or_false]

/-- Adaptedness of the actual countable step process follows term by term
from stopped-value measurability. Coefficients before their stopping time
are never presumed to be measurable at the current time. -/
theorem partition_step_adapted
    {Ω : Type*} {T : EReal} [Fact (0 ≤ T)]
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F)
    (H : ClosedTime T → Ω → ℝ)
    (hm : ∀ t, t < ⊤ → Measurable[F t] (H t))
    (hc : ∀ ω t, t < ⊤ → ContinuousAt (fun s => H s ω) t)
    (c : ℕ → ClosedTime T) (hcm : Monotone c) (hct : ∀ n, c n < ⊤)
    (hcc : ∀ t, t < ⊤ → ∃ n, t < c n)
    (τ : ℕ → Ω → ClosedTime T)
    (hτ : ∀ j t, MeasurableSet[F t] {ω | τ j ω ≤ t}) (hτt : ∀ j ω, τ j ω < ⊤) :
    ∀ t, Measurable[F t] (fun ω => partitionStep (fun s => H s ω) (fun j => τ j ω) t) := by
  intro t
  letI : MeasurableSpace Ω := F t
  apply Measurable.tsum
  intro j
  have he : MeasurableSet[F t] {ω | τ j ω < t ∧ t ≤ τ (j+1) ω} := by
    convert (strict_stopping_event_measurable F hF (τ j) (hτ j) t).inter
        (strict_stopping_event_measurable F hF (τ (j+1)) (hτ (j+1)) t).compl using 1
    ext ω
    simp only [mem_setOf_eq,mem_inter_iff,mem_compl_iff,not_lt]
  have hstop := (open_continuous_adapted_stopped_regular F hF H hm hc c hcm hct hcc
    (τ j) (hτ j) (hτt j)).1 t
  convert hstop.indicator he using 1
  funext ω
  by_cases hω : τ j ω < t ∧ t ≤ τ (j+1) ω
  · simp only [Set.indicator,mem_Ioc,mem_setOf_eq,if_pos hω,min_eq_left hω.1.le]
  · simp only [Set.indicator,mem_Ioc,mem_setOf_eq,if_neg hω]

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.partition_step_left_continuous
#print axioms Asakura.Chapter3Complete.strict_stopping_event_measurable
#print axioms Asakura.Chapter3Complete.partition_step_adapted

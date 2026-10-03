import Chapter3PartitionStepRegularity
import Chapter2ContinuousIntegrand
import Chapter2StoppingIntegrandMembership

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- Progressive measurability of the countable stopping-partition step
integrand. Each summand is a stopped continuous adapted process restricted
to its stochastic interval, exactly as in the manuscript. -/
theorem partition_step_prefix_progressive
    {Ω : Type*} {T : EReal} [Fact (0 ≤ T)]
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F)
    (H : ClosedTime T → Ω → ℝ)
    (hm : ∀ t, t < ⊤ → Measurable[F t] (H t))
    (hc : ∀ ω t, t < ⊤ → ContinuousAt (fun s => H s ω) t)
    (c : ℕ → ClosedTime T) (hcm : Monotone c) (hct : ∀ n, c n < ⊤)
    (hcc : ∀ t, t < ⊤ → ∃ n, t < c n)
    (τ : ℕ → Ω → ClosedTime T)
    (hτ : ∀ j t, MeasurableSet[F t] {ω | τ j ω ≤ t}) (hτt : ∀ j ω, τ j ω < ⊤)
    (b : ℝ) (hb : 0 ≤ b) :
    @Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) b => F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) b => partitionStep (fun s => H s z.1) (fun j => τ j z.1) (realTimeClamp z.2.val)) := by
  letI : MeasurableSpace (Ω × Icc (0:ℝ) b) :=
    progressiveSpace (fun t : Icc (0:ℝ) b => F (realTimeClamp t.val))
  apply Measurable.tsum
  intro j
  have hstop := open_continuous_adapted_stopped_regular F hF H hm hc c hcm hct hcc
    (τ j) (hτ j) (hτt j)
  have hp := continuous_adapted_real_progressive F hF
    (fun z : Ω × ℝ => H (min (τ j z.1) (realTimeClamp z.2)) z.1) b hb
    (fun r _ => hstop.1 (realTimeClamp r))
    (fun ω => ((hstop.2 ω).comp real_time_clamp_continuous).continuousOn)
  have hi := stopping_interval_prefix_progressive F hF (τ j) (τ (j+1)) (hτ j) (hτ (j+1)) b
    (fun z : Ω × ℝ => H (min (τ j z.1) (realTimeClamp z.2)) z.1) hp
  convert hi using 1
  funext z
  by_cases hz : realTimeClamp (T := T) z.2.val ∈ Ioc (τ j z.1) (τ (j+1) z.1)
  · simp only [indicator_of_mem hz,min_eq_left hz.1.le]
  · simp only [indicator_of_notMem hz]

/-- Path measurability of the step process does not require measurability
of H on the full time domain: its coefficients are constant on intervals. -/
theorem partition_step_measurable
    {T : EReal} [Fact (0 ≤ T)] (H : ClosedTime T → ℝ) (τ : ℕ → ClosedTime T) :
    Measurable (partitionStep H τ) := by
  apply Measurable.tsum
  intro j
  exact measurable_const.indicator measurableSet_Ioc

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.partition_step_prefix_progressive
#print axioms Asakura.Chapter3Complete.partition_step_measurable

import Chapter2StochasticIntervalMembership

open MeasureTheory Set Filter
open scoped Topology ENNReal Classical
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option backward.isDefEq.respectTransparency false

/-- Prefix progressiveness in the manuscript's stopping-time coordinates. -/
theorem stopping_interval_prefix_progressive
    {Ω : Type*} {T : EReal} [Fact (0 ≤ T)]
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F)
    (σ τ : Ω → ClosedTime T)
    (hσ : ∀ t, MeasurableSet[F t] {ω | σ ω ≤ t})
    (hτ : ∀ t, MeasurableSet[F t] {ω | τ ω ≤ t})
    (b : ℝ) (H : Ω × ℝ → ℝ)
    (hH : @Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) b => F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) b => H (z.1,z.2.val))) :
    @Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) b => F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) b =>
        (Ioc (σ z.1) (τ z.1)).indicator (fun _ => H (z.1,z.2.val)) (realTimeClamp z.2.val)) := by
  have hg := stochastic_interval_progressive F hF σ τ hσ hτ
  have hi : @MeasurableSet (Ω × Icc (0:ℝ) b)
      (progressiveSpace (fun t : Icc (0:ℝ) b => F (realTimeClamp t.val)))
      {z | σ z.1 < realTimeClamp z.2.val ∧ realTimeClamp z.2.val ≤ τ z.1} := by
    apply MeasurableSpace.measurableSet_iInf.mpr
    intro t
    letI : MeasurableSpace Ω := F (realTimeClamp t.val)
    let q : Iic t → Iic (realTimeClamp (T := T) t.val) := fun s =>
      ⟨realTimeClamp s.val.val,real_time_clamp_mono s.property⟩
    have hq : Measurable q :=
      ((real_time_clamp_continuous.measurable.comp measurable_subtype_coe).comp measurable_subtype_coe).subtype_mk
    have hs := MeasurableSpace.measurableSet_iInf.mp hg (realTimeClamp t.val)
    exact (measurable_fst.prodMk (hq.comp measurable_snd)) hs
  convert hH.indicator hi using 1
  funext z
  simp only [indicator_apply,mem_setOf_eq,mem_Ioc]

/-- Restriction to ((sigma,tau]] preserves both local L1(dV) and L2(dQ).
The measures need not be deterministic or finite for this assertion. -/
theorem stopping_interval_integrability
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {T : EReal} [Fact (0 ≤ T)] (σ τ : Ω → ClosedTime T)
    (κ β : ℕ → Ω → Measure ℝ) (H : Ω × ℝ → ℝ)
    (hκ : ∀ n, ∀ᵐ ω ∂P, Integrable (fun r => H (ω,r)) (κ n ω))
    (hβ : ∀ n, ∀ᵐ ω ∂P, Integrable (fun r => H (ω,r)^2) (β n ω)) :
    (∀ n, ∀ᵐ ω ∂P, Integrable
      (fun r => (Ioc (σ ω) (τ ω)).indicator (fun _ => H (ω,r)) (realTimeClamp r)) (κ n ω)) ∧
    (∀ n, ∀ᵐ ω ∂P, Integrable
      (fun r => ((Ioc (σ ω) (τ ω)).indicator (fun _ => H (ω,r)) (realTimeClamp r))^2) (β n ω)) := by
  have hm ω : MeasurableSet {r : ℝ | realTimeClamp (T := T) r ∈ Ioc (σ ω) (τ ω)} :=
    real_time_clamp_continuous.measurable measurableSet_Ioc
  constructor
  · intro n
    filter_upwards [hκ n] with ω hi
    convert hi.indicator (hm ω) using 1
    funext r
    simp only [indicator_apply,mem_setOf_eq]
  · intro n
    filter_upwards [hβ n] with ω hi
    convert hi.indicator (hm ω) using 1
    funext r
    by_cases hr : realTimeClamp (T := T) r ∈ Ioc (σ ω) (τ ω)
    · rw [indicator_of_mem hr,indicator_of_mem (show r ∈ {r : ℝ | realTimeClamp (T := T) r ∈ Ioc (σ ω) (τ ω)} from hr)]
    · rw [indicator_of_notMem hr,indicator_of_notMem (show r ∉ {r : ℝ | realTimeClamp (T := T) r ∈ Ioc (σ ω) (τ ω)} from hr)]
      norm_num

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.stopping_interval_prefix_progressive
#print axioms Asakura.Chapter2Complete.stopping_interval_integrability

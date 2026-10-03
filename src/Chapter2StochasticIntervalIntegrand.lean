import Chapter2ProgressiveSpace
import Chapter2SignedCumulativeVariation

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

/-- Progressive measurability of the stochastic interval ((sigma,tau]].
This follows directly from measurable stopped times, without imposing
right continuity on its left-continuous indicator process. -/
theorem stochastic_interval_progressive
    {Ω : Type*} {T : EReal} (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F)
    (σ τ : Ω → ClosedTime T)
    (hσ : ∀ t, MeasurableSet[F t] {ω | σ ω ≤ t})
    (hτ : ∀ t, MeasurableSet[F t] {ω | τ ω ≤ t}) :
    @MeasurableSet (Ω × ClosedTime T) (progressiveSpace F)
      {z | σ z.1 < z.2 ∧ z.2 ≤ τ z.1} := by
  apply MeasurableSpace.measurableSet_iInf.mpr
  intro t
  letI : MeasurableSpace Ω := F t
  change MeasurableSet {z : Ω × Iic t | σ z.1 < z.2.val ∧ z.2.val ≤ τ z.1}
  have hs : Measurable (fun z : Ω × Iic t => min (σ z.1) t) := (stopped_min_measurable F hF σ hσ t).comp measurable_fst
  have ht : Measurable (fun z : Ω × Iic t => min (τ z.1) t) := (stopped_min_measurable F hF τ hτ t).comp measurable_fst
  have htime : Measurable (fun z : Ω × Iic t => z.2.val) := measurable_subtype_coe.comp measurable_snd
  have hm := (measurableSet_lt hs htime).inter (measurableSet_le htime ht)
  convert hm using 1
  ext z
  simp only [mem_setOf_eq,mem_inter_iff,min_lt_iff,le_min_iff]
  have hz := z.2.property
  constructor
  · rintro ⟨ha,hb⟩; exact ⟨Or.inl ha,hb,hz⟩
  · rintro ⟨ha,hb,hc⟩
    exact ⟨ha.resolve_right (not_lt_of_ge hz),hb⟩

theorem stochastic_interval_integrand_progressive
    {Ω : Type*} {T : EReal} (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F)
    (σ τ : Ω → ClosedTime T)
    (hσ : ∀ t, MeasurableSet[F t] {ω | σ ω ≤ t})
    (hτ : ∀ t, MeasurableSet[F t] {ω | τ ω ≤ t})
    (H : Ω × ClosedTime T → ℝ)
    (hH : @Measurable _ _ (progressiveSpace F) inferInstance H) :
    @Measurable _ _ (progressiveSpace F) inferInstance
      ({z | σ z.1 < z.2 ∧ z.2 ≤ τ z.1}.indicator H) :=
  hH.indicator (stochastic_interval_progressive F hF σ τ hσ hτ)

/-- The finite-variation part of exercise rep263, for the actual signed
integral and exactly the open-left, closed-right stochastic interval. -/
theorem signed_cumulative_stochastic_interval (ν : SignedMeasure ℝ) (f : ℝ → ℝ)
    (hf : Integrable f ν.totalVariation) (σ τ t : ℝ) (hστ : σ ≤ τ) :
    signedCumulative ν ((Ioc σ τ).indicator f) t =
      signedCumulative ν f (min τ t)-signedCumulative ν f (min σ t) := by
  rw [signed_cumulative_increment ν f hf _ _ (min_le_min_right t hστ)]
  change signedIntegralRaw ν ((Iic t).indicator ((Ioc σ τ).indicator f)) = _
  congr 1
  funext r
  by_cases hrσ : σ < r
  · by_cases hrτ : r ≤ τ
    · by_cases hrt : r ≤ t <;> simp [Set.indicator,hrσ,hrτ,hrt,min_lt_iff,le_min_iff]
    · by_cases hrt : r ≤ t <;> simp [Set.indicator,hrσ,hrτ,hrt,min_lt_iff,le_min_iff]
  · have hnot : ¬ (min σ t < r ∧ r ≤ min τ t) := by
      rintro ⟨hlo,hhi⟩
      rcases min_lt_iff.mp hlo with hs | ht
      · exact hrσ hs
      · exact (not_lt_of_ge (le_min_iff.mp hhi).2) ht
    simp only [indicator_of_notMem (show r ∉ Ioc (min σ t) (min τ t) from hnot)]
    by_cases hrt : r ∈ Iic t <;> simp [Set.indicator,hrt,hrσ]

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.stochastic_interval_progressive
#print axioms Asakura.Chapter2Complete.signed_cumulative_stochastic_interval

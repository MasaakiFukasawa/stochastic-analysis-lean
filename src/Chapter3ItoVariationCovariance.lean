import Chapter3ItoVariationEnergy
import Chapter2SignedRestriction

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- The covariance characterization agrees with the actual signed variation
integral, also for cross-covariations, whose measures need not be positive. -/
theorem ito_covariance_identified_with_variation_integral
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω)
    (X Y N C I : ClosedTime T → Ω → ℝ)
    (hY : LocalMProcessWitness P F Y) (hN : LocalMProcessWitness P F N)
    (hC : LocalCovarianceWitness P F X N C)
    (H : Ω × ℝ → ℝ) (hHm : ∀ ω, Measurable (fun r => H (ω,r)))
    (hYI : ItoCovarianceFormula P F X H Y)
    (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n) (hcT : ∀ n, (c n:EReal) < T)
    (hcc : ∀ t, t < ⊤ → ∃ n, t < realTimeClamp (T := T) (c n))
    (hIc : ∀ ω t, t < ⊤ → ContinuousAt (fun s => I s ω) t)
    (hI : VariationIntegralFormula P c hc C H I) :
    ∃ D, LocalCovarianceWitness P F Y N D ∧
      ∀ᵐ ω ∂P, ∀ t, t < ⊤ → D t ω = I t ω := by
  obtain ⟨D,hD,hd⟩ := hYI N C hN hC
  refine ⟨D,hD,?_⟩
  have he t (ht : t < ⊤) : D t =ᵐ[P] I t := by
    obtain ⟨d,hd0,hdT,rfl⟩ := finite_closed_time_real t ht
    obtain ⟨j,hj⟩ := hcc (realTimeClamp d) ht
    have hdj : d ≤ c j := by
      change (realTimeClamp d : EReal) < (realTimeClamp (c j) : EReal) at hj
      rw [real_time_clamp_eq d hd0 hdT.le,real_time_clamp_eq (c j) (hc j) (hcT j).le] at hj
      exact (EReal.coe_lt_coe_iff.mp hj).le
    obtain ⟨ν,hν,hν0,_,hνD⟩ := hd d hd0 hdT
    obtain ⟨κ,hs,hκ,hi,hform⟩ := hI j
    filter_upwards [hν0,hνD,hs,hκ,hi,hform] with ω hν0ω hDω hsω hκω hiω hfω
    have hκ0 : (κ ω).totalVariation (Iic 0) = 0 := by
      apply measure_mono_null (show Iic (0:ℝ) ⊆ (Ioc 0 (c j))ᶜ from fun r hr h => not_lt_of_ge hr h.1)
      exact ae_iff.mp hsω
    have hclip r (hr : 0 ≤ r) : intervalClamp 0 (c j) (hc j) r = min r (c j) := by
      by_cases hrj : r ≤ c j
      · rw [intervalClamp_eq 0 (c j) (hc j) ⟨hr,hrj⟩,min_eq_left hrj]
      · simp only [intervalClamp,projIcc_of_right_le (hc j) (le_of_not_ge hrj),min_eq_right (le_of_not_ge hrj)]
    have hmin a b : realTimeClamp (T := T) (min a b) = min (realTimeClamp a) (realTimeClamp b) := by
      rcases le_total a b with h | h
      · rw [min_eq_left h,min_eq_left (real_time_clamp_mono h)]
      · rw [min_eq_right h,min_eq_right (real_time_clamp_mono h)]
    have heν : ν ω = (κ ω).restrict (Iic d) := by
      apply signed_stopped_interval_consistency (fun r => C (realTimeClamp r) ω) (c j) d hd0 hdj
        (ν ω) (κ ω) hν0ω hκ0
      · intro a b ha hab
        simpa only [hmin] using hν ω a b ha hab
      · intro a b ha hab
        rw [hκω a b hab,hclip a ha,hclip b (ha.trans hab)]
    have hie := hfω (realTimeClamp d)
    rw [min_eq_right (real_time_clamp_mono hdj),finite_prefix_time_of_real (c j) d (hc j)
      ⟨hd0,hdj⟩ (hcT j).le] at hie
    rw [hDω,heν,signed_integral_restrict (κ ω) measurableSet_Iic _ (hHm ω) hiω.integrableOn]
    exact hie.symm
  letI : Nonempty (Iio (⊤ : ClosedTime T)) := ⟨⟨⊥,hT⟩⟩
  have hall := continuous_process_common_time_equality P
    (fun t : Iio (⊤ : ClosedTime T) => D t.val)
    (fun t : Iio (⊤ : ClosedTime T) => I t.val)
    (hD.continuous_open_paths P F Y N D hY hN)
    (fun ω => continuous_iff_continuousAt.mpr (fun t =>
      (hIc ω t.val t.property).comp continuous_subtype_val.continuousAt))
    (fun t => he t.val t.property)
  exact hall.mono (fun ω hω t ht => hω ⟨t,ht⟩)

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.ito_covariance_identified_with_variation_integral

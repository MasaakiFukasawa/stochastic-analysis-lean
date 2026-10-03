import Chapter2ItoCovarianceProcessFormula
import Chapter3ContinuousIntegralConstruction

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter6
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- The bracket of an Ito integral with another local martingale is
identified with the actual signed Stieltjes integral, on all finite times. -/
theorem ito_covariance_variation_identity
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)]
    (F : ClosedTime T → MeasurableSpace Ω)
    (X Y L C J : ClosedTime T → Ω → ℝ)
    (hY : LocalMProcessWitness P F Y) (hL : LocalMProcessWitness P F L)
    (hC : LocalCovarianceWitness P F X Y C)
    (H : Ω × ℝ → ℝ) (hHm : ∀ w,Measurable (fun r => H (w,r)))
    (hLInt : ItoCovarianceFormula P F X H L)
    (c : ℕ → ℝ) (hc : ∀ n,0 ≤ c n) (hcT : ∀ n,(c n:EReal) < T)
    (hcc : ∀ t,t < ⊤ → ∃ n,t < realTimeClamp (T := T) (c n))
    (hJ : VariationIntegralFormula P c hc C H J) :
    ∃ D,LocalCovarianceWitness P F L Y D ∧
      ∀ᵐ w ∂P,∀ t,t < ⊤ → D t w = J t w := by
  obtain ⟨D,hD,hform⟩ := hLInt.finite_process_formula P F X L H hL hHm Y C hY hC
  refine ⟨D,hD,?_⟩
  have he n : ∀ᵐ w ∂P,∀ t,D (min (realTimeClamp (c n)) t) w = J (min (realTimeClamp (c n)) t) w := by
    obtain ⟨ν,hν,hν0,_,hνD⟩ := hform (c n) (hc n) (hcT n)
    obtain ⟨κ,hks,hκ,_,hκJ⟩ := hJ n
    filter_upwards [hν0,hνD,hks,hκ,hκJ] with w hn0 hnD hks hk hkJ
    have hz : (κ w).totalVariation {r : ℝ | r ∉ Ioc 0 (c n)} = 0 := ae_iff.mp hks
    have hk0 : (κ w).totalVariation (Iic 0) = 0 := by
      apply measure_mono_null (show Iic (0:ℝ) ⊆ {r : ℝ | r ∉ Ioc 0 (c n)} from
        fun r hr hm => not_lt_of_ge hr hm.1) hz
    have hclamp r (hr : 0 ≤ r) : intervalClamp 0 (c n) (hc n) r = min r (c n) := by
      by_cases hrn : r ≤ c n
      · rw [intervalClamp_eq 0 (c n) (hc n) ⟨hr,hrn⟩,min_eq_left hrn]
      · simp only [intervalClamp,projIcc_of_right_le (hc n) (le_of_not_ge hrn),min_eq_right (le_of_not_ge hrn)]
    have hνκ : ν w = κ w := by
      apply signed_measure_ext_positive_Ioc _ _ hn0 hk0
      intro a b ha hab
      rw [hν w a b ha hab,hk a b hab,hclamp b (ha.trans hab),hclamp a ha,
        real_time_clamp_mono.map_min,real_time_clamp_mono.map_min]
    intro t
    have hh := hnD (finitePrefixTime (c n) (hc n) t).val (finitePrefixTime (c n) (hc n) t).property
    rw [hνκ] at hh
    rw [hkJ t]
    simpa only [finite_prefix_time_clamp (c n) (hc n) (hcT n).le] using hh
  filter_upwards [ae_all_iff.mpr he] with w hw
  intro t ht
  obtain ⟨n,hn⟩ := hcc t ht
  simpa only [min_eq_right hn.le] using hw n t

end Asakura.Chapter6

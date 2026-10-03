import Chapter6VariationScaling

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter6
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1600000

/-- Additivity of the actual variation integral, with equality of its
signed measures proved from the interval increments. -/
theorem variation_integrand_add
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {T : EReal} [Fact (0 ≤ T)] (c : ℕ → ℝ) (hc : ∀ n,0 ≤ c n)
    (A I J : ClosedTime T → Ω → ℝ) (H G : Ω × ℝ → ℝ)
    (hI : VariationIntegralFormula P c hc A H I)
    (hJ : VariationIntegralFormula P c hc A G J) :
    VariationIntegralFormula P c hc A (fun z => H z+G z) (fun t w => I t w+J t w) := by
  intro n
  obtain ⟨ν,hs,hν,hi,hform⟩ := hI n
  obtain ⟨κ,_,hκ,hj,hformJ⟩ := hJ n
  have he : ∀ᵐ w ∂P,ν w = κ w := by
    filter_upwards [hν,hκ] with w hn hk
    exact signed_measure_ext_Ioc _ _ (fun a b hab => (hn a b hab.le).trans (hk a b hab.le).symm)
  have hj' : ∀ᵐ w ∂P,Integrable (fun r => G (w,r)) (ν w).totalVariation := by
    filter_upwards [he,hj] with w hw hj
    rwa [hw]
  refine ⟨ν,hs,hν,?_,?_⟩
  · filter_upwards [hi,hj'] with w hi hj
    exact hi.add hj
  · filter_upwards [hi,hj',hform,hformJ,he] with w hi hj hf hfJ he
    intro t
    rw [hf t,hfJ t,← he]
    unfold signedCumulative
    have hh := signed_integral_add_smul (ν w)
      ((Iic (finitePrefixTime (c n) (hc n) t).val).indicator (fun r => H (w,r)))
      ((Iic (finitePrefixTime (c n) (hc n) t).val).indicator (fun r => G (w,r)))
      (hi.indicator measurableSet_Iic) (hj.indicator measurableSet_Iic) 1
    simp only [one_mul] at hh
    rw [← hh]
    congr 1
    funext r
    by_cases hr : r ∈ Iic (finitePrefixTime (c n) (hc n) t).val <;> simp [hr]

end Asakura.Chapter6

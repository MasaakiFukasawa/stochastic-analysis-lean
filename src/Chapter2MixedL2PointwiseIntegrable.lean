import Chapter2L2FubiniMinkowski

open MeasureTheory Set
open scoped ENNReal
namespace Asakura.Chapter2Complete
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

/-- The pointwise parameter integral in stochastic Fubini is an ordinary
absolutely convergent integral almost everywhere, not merely Lean's totalized
integral of a possibly nonintegrable function. -/
theorem mixed_l1_l2_pointwise_integrable
    {E S : Type*} [MeasurableSpace E] [MeasurableSpace S]
    (μ : Measure E) [SigmaFinite μ] (ν : Measure S) [SigmaFinite ν]
    (H : E × S → ℝ) (hH : Measurable H)
    (hN : (∫⁻ x, eLpNorm (fun r => H (x,r)) 2 ν ∂μ) < ∞) :
    ∀ᵐ r ∂ν, Integrable (fun x => H (x,r)) μ := by
  obtain ⟨hI,hgood,_⟩ := integrable_l2Section μ ν H hH hN
  apply ae_of_forall_measure_lt_top_ae_restrict
  intro B hB hfin
  letI : IsFiniteMeasure (ν.restrict B) := ⟨by simpa using hfin⟩
  have hprod : Integrable H (μ.prod (ν.restrict B)) := by
    apply (integrable_prod_iff hH.aestronglyMeasurable).mpr
    constructor
    · filter_upwards [hgood] with x hx
      exact ((hx.choose).restrict B).integrable (by norm_num)
    · apply (hI.norm.const_mul ‖indicatorConstLp 2 hB hfin.ne (1:ℝ)‖).mono'
        (hH.norm.stronglyMeasurable.integral_prod_right').aestronglyMeasurable
      filter_upwards [hgood] with x hx
      rw [Real.norm_eq_abs,abs_of_nonneg (integral_nonneg (fun r => norm_nonneg _)),hx.choose_spec]
      exact l2_set_integral_norm_bound ν B hB hfin.ne _ hx.choose
  exact hprod.prod_left_ae

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.mixed_l1_l2_pointwise_integrable

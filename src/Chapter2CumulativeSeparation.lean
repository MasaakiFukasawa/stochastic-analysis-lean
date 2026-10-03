import Chapter2CumulativeIntegral
import Mathlib.MeasureTheory.VectorMeasure.WithDensity

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/-- Vanishing of every cumulative integral implies vanishing of its
density. This is the signed-measure separation step in the density proof. -/
theorem integrand_zero_of_cumulative_integrals_zero
    (μ : Measure ℝ) (g : ℝ → ℝ) (hg : Integrable g μ)
    (hz : ∀ t, (∫ x in Iic t, g x ∂μ) = 0) : g =ᵐ[μ] 0 := by
  have hlim : Tendsto (fun n : ℕ => ∫ x, (Iic (n:ℝ)).indicator g x ∂μ) atTop
      (𝓝 (∫ x, g x ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => ‖g x‖)
      (fun n => hg.aestronglyMeasurable.indicator measurableSet_Iic) hg.norm ?_ ?_
    · intro n
      exact .of_forall fun x => by by_cases h : x ∈ Iic (n:ℝ) <;> simp [Set.indicator,h]
    · apply Filter.Eventually.of_forall
      intro x
      obtain ⟨N,hN⟩ := exists_nat_ge x
      apply tendsto_const_nhds.congr'
      refine eventually_atTop.2 ⟨N,fun n hn => ?_⟩
      exact (indicator_of_mem (show x ∈ Iic (n:ℝ) from hN.trans (by exact_mod_cast hn)) g).symm
  have htotal : (∫ x, g x ∂μ) = 0 := by
    simp only [integral_indicator measurableSet_Iic,hz] at hlim
    exact tendsto_nhds_unique hlim tendsto_const_nhds
  apply (hg.withDensityᵥ_eq_iff (integrable_zero _ _ _)).1
  apply VectorMeasure.ext_of_generateFrom (range Iic)
  · rintro S ⟨t,rfl⟩
    rw [withDensityᵥ_apply hg measurableSet_Iic,
      withDensityᵥ_apply (integrable_zero _ _ _) measurableSet_Iic,hz]
    simp
  · exact borel_eq_generateFrom_Iic ℝ
  · exact isPiSystem_Iic
  · rw [withDensityᵥ_apply hg MeasurableSet.univ,
      withDensityᵥ_apply (integrable_zero _ _ _) MeasurableSet.univ]
    simpa only [setIntegral_univ,Pi.zero_apply,integral_zero] using htotal

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.integrand_zero_of_cumulative_integrals_zero

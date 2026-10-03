import Chapter2M2TerminalRealization

open MeasureTheory Set
open scoped ENNReal
namespace Asakura.Chapter2Complete
set_option maxHeartbeats 1100000
set_option backward.isDefEq.respectTransparency false

/-- The probabilistic Cauchy-Schwarz step after the pathwise covariation
bound, with the square-root integrability justified explicitly. -/
theorem integrable_sqrt_product_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (A B : Ω → ℝ)
    (hA : Integrable A P) (hB : Integrable B P)
    (hA0 : ∀ᵐ ω ∂P, 0 ≤ A ω) (hB0 : ∀ᵐ ω ∂P, 0 ≤ B ω) :
    Integrable (fun ω => Real.sqrt (A ω)*Real.sqrt (B ω)) P ∧
      (∫ ω, Real.sqrt (A ω)*Real.sqrt (B ω) ∂P) ≤
        Real.sqrt (∫ ω, A ω ∂P)*Real.sqrt (∫ ω, B ω ∂P) := by
  have hAm := Real.continuous_sqrt.comp_aestronglyMeasurable hA.aestronglyMeasurable
  have hBm := Real.continuous_sqrt.comp_aestronglyMeasurable hB.aestronglyMeasurable
  have hAe : (fun ω => Real.sqrt (A ω)^2) =ᵐ[P] A := hA0.mono (fun ω hω => Real.sq_sqrt hω)
  have hBe : (fun ω => Real.sqrt (B ω)^2) =ᵐ[P] B := hB0.mono (fun ω hω => Real.sq_sqrt hω)
  have hAL : MemLp (fun ω => Real.sqrt (A ω)) 2 P :=
    (memLp_two_iff_integrable_sq hAm).mpr (hA.congr hAe.symm)
  have hBL : MemLp (fun ω => Real.sqrt (B ω)) 2 P :=
    (memLp_two_iff_integrable_sq hBm).mpr (hB.congr hBe.symm)
  refine ⟨hAL.integrable_mul hBL,?_⟩
  have he : (∫ ω, Real.sqrt (A ω)*Real.sqrt (B ω) ∂P) =
      inner ℝ (hAL.toLp _) (hBL.toLp _) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hAL.coeFn_toLp,hBL.coeFn_toLp] with ω ha hb
    rw [Real.inner_apply,ha,hb]
  have hAn : ‖hAL.toLp (fun ω => Real.sqrt (A ω))‖ = Real.sqrt (∫ ω, A ω ∂P) := by
    have hh := real_l2_norm_sq_integral P _ hAL
    rw [integral_congr_ae hAe] at hh
    rw [← hh,Real.sqrt_sq (norm_nonneg _)]
  have hBn : ‖hBL.toLp (fun ω => Real.sqrt (B ω))‖ = Real.sqrt (∫ ω, B ω ∂P) := by
    have hh := real_l2_norm_sq_integral P _ hBL
    rw [integral_congr_ae hBe] at hh
    rw [← hh,Real.sqrt_sq (norm_nonneg _)]
  rw [he,← hAn,← hBn]
  exact real_inner_le_norm _ _

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.integrable_sqrt_product_bound

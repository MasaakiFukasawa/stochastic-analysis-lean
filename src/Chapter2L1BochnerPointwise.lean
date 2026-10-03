import Chapter2CovarianceBochnerExchange
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.AEEqOfIntegral

open MeasureTheory Set Filter
open scoped Topology ENNReal Classical
namespace Asakura.Chapter2Complete
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

noncomputable def l1SetIntegralCLM {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (B : Set Ω) : Lp ℝ 1 P →L[ℝ] ℝ :=
  L1.integralCLM.comp (LpToLpRestrictCLM Ω ℝ ℝ P 1 B)

theorem l1_set_integral_clm_apply {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (B : Set Ω) (f : Lp ℝ 1 P) :
    l1SetIntegralCLM P B f = ∫ ω in B, f ω ∂P := by
  change L1.integralCLM (LpToLpRestrictCLM Ω ℝ ℝ P 1 B f) = _
  rw [← L1.integral_eq,L1.integral_eq_integral]
  exact integral_congr_ae (LpToLpRestrictCLM_coeFn ℝ B f)

/-- Identify the Bochner integral in the covariance operator's L1 codomain
with the pointwise parameter integral, using all measurable set integrals. -/
theorem l1_bochner_integral_pointwise
    {E Ω : Type*} [MeasurableSpace E] [MeasurableSpace Ω]
    (μ : Measure E) [SigmaFinite μ] (P : Measure Ω) [SigmaFinite P]
    (Z : E → Lp ℝ 1 P) (hZ : Integrable Z μ)
    (g : E × Ω → ℝ) (hg : Integrable g (μ.prod P))
    (he : ∀ᵐ x ∂μ, (Z x : Ω → ℝ) =ᵐ[P] (fun ω => g (x,ω))) :
    ((∫ x, Z x ∂μ : Lp ℝ 1 P) : Ω → ℝ) =ᵐ[P] (fun ω => ∫ x, g (x,ω) ∂μ) := by
  apply Integrable.ae_eq_of_forall_setIntegral_eq _ _
    (L1.integrable_coeFn _) hg.integral_prod_right
  intro B hB hfin
  rw [← l1_set_integral_clm_apply P B,← (l1SetIntegralCLM P B).integral_comp_comm hZ]
  simp_rw [l1_set_integral_clm_apply]
  have hgB : Integrable g (μ.prod (P.restrict B)) :=
    hg.mono_measure (Measure.prod_mono le_rfl Measure.restrict_le_self)
  rw [← integral_integral_swap (f := fun x ω => g (x,ω)) hgB]
  apply integral_congr_ae
  filter_upwards [he] with x hx
  exact integral_congr_ae (ae_restrict_of_ae hx)

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.l1_bochner_integral_pointwise

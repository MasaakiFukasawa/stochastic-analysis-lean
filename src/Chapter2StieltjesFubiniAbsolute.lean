import Chapter2FubiniAbsoluteBound
import Chapter2RandomSignedVariation
import Chapter2SignedFubini
import Chapter2FiniteKernelIntegrability

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal Classical
namespace Asakura.Chapter2Complete
open Asakura.FullAudit
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

/-- The printed ordinary-Fubini step for random covariance measures:
absolute integrability is derived from interval CS and the mixed energy
norm, then Fubini is applied to the actual signed integrals. -/
theorem stieltjes_fubini_absolute_integrability
    {E Ω : Type*} [MeasurableSpace E] [MeasurableSpace Ω]
    (μ : Measure E) [SigmaFinite μ] (P : Measure Ω) [IsProbabilityMeasure P]
    (α β : Ω → Measure ℝ) [∀ ω, IsFiniteMeasure (α ω)] [∀ ω, IsFiniteMeasure (β ω)]
    (ν : Ω → SignedMeasure ℝ) (hν : Measurable (fun ω => (ν ω).totalVariation))
    (hc : ∀ᵐ ω ∂P, ∀ s t, s ≤ t → |ν ω (Ioc s t)| ≤
      Real.sqrt ((α ω).real (Ioc s t))*Real.sqrt ((β ω).real (Ioc s t)))
    (H : (E × Ω) × ℝ → ℝ) (hH : Measurable H)
    (hi : ∀ᵐ x ∂μ, ∀ᵐ ω ∂P, Integrable (fun r => H ((x,ω),r)^2) (α ω))
    (hAi : ∀ᵐ x ∂μ, Integrable (fun ω => ∫ r, H ((x,ω),r)^2 ∂α ω) P)
    (hBi : Integrable (fun ω => (β ω).real univ) P)
    (hN : Integrable (fun x => Real.sqrt (∫ ω, ∫ r, H ((x,ω),r)^2 ∂α ω ∂P)) μ) :
    Integrable (fun z : E × Ω => ∫ r, |H (z,r)| ∂(ν z.2).totalVariation) (μ.prod P) ∧
      (∫ ω, ∫ x, ∫ r, |H ((x,ω),r)| ∂(ν ω).totalVariation ∂μ ∂P) ≤
        (∫ x, Real.sqrt (∫ ω, ∫ r, H ((x,ω),r)^2 ∂α ω ∂P) ∂μ)*
          Real.sqrt (∫ ω, (β ω).real univ ∂P) ∧
      ∀ᵐ ω ∂P, Integrable (fun z : E × ℝ => H ((z.1,ω),z.2)) (μ.prod (ν ω).totalVariation) ∧
        (∫ x, signedIntegralRaw (ν ω) (fun r => H ((x,ω),r)) ∂μ) =
          signedIntegralRaw (ν ω) (fun r => ∫ x, H ((x,ω),r) ∂μ) := by
  let V := fun z : E × Ω => ∫ r, |H (z,r)| ∂(ν z.2).totalVariation
  let κ : Kernel (E × Ω) ℝ := ⟨fun z => (ν z.2).totalVariation,hν.comp measurable_snd⟩
  have hκ z : IsFiniteMeasure (κ z) := show IsFiniteMeasure (ν z.2).totalVariation from inferInstance
  have hVm : Measurable V := finite_kernel_integral_measurable κ hκ _
    (by simpa only [Real.norm_eq_abs] using hH.norm)
  have hHm x ω : Measurable (fun r => H ((x,ω),r)) := hH.comp measurable_prodMk_left
  have hpath : ∀ᵐ x ∂μ, ∀ᵐ ω ∂P, Integrable (fun r => H ((x,ω),r)) (ν ω).totalVariation ∧
      V (x,ω) ≤ Real.sqrt (∫ r, H ((x,ω),r)^2 ∂α ω)*Real.sqrt ((β ω).real univ) := by
    filter_upwards [hi] with x hix
    filter_upwards [hix,hc] with ω hiω hcω
    exact signed_stieltjes_absolute_integral_bound (α ω) (β ω) (ν ω) hcω _ (hHm x ω) hiω
  obtain ⟨hVi,hbound⟩ := fubini_kw_expectation_bound μ P
    (fun z => ∫ r, H (z,r)^2 ∂α z.2) V (fun ω => (β ω).real univ) hVm
    (fun z => integral_nonneg (fun r => abs_nonneg _)) hAi
    (.of_forall (fun x => .of_forall (fun ω => integral_nonneg (fun r => sq_nonneg _))))
    hBi (.of_forall (fun ω => measureReal_nonneg))
    (hpath.mono (fun x hx => hx.mono (fun ω hω => hω.2))) hN
  refine ⟨hVi,?_,?_⟩
  · have he : (∫ ω, ∫ x, V (x,ω) ∂μ ∂P) = ∫ z, V z ∂μ.prod P :=
      (integral_prod_symm V hVi).symm
    exact he.trans_le hbound
  · have hpath' : ∀ᵐ ω ∂P, ∀ᵐ x ∂μ, Integrable (fun r => H ((x,ω),r)) (ν ω).totalVariation :=
      (Measure.ae_ae_comm (finite_kernel_integrable_set_measurable κ hκ H hH)).mp
        (hpath.mono (fun x hx => hx.mono (fun ω hω => hω.1)))
    filter_upwards [hVi.prod_left_ae,hpath'] with ω hvω hiω
    have hmω : Measurable (fun z : E × ℝ => H ((z.1,ω),z.2)) :=
      hH.comp ((measurable_fst.prodMk measurable_const).prodMk measurable_snd)
    have hiω' : Integrable (fun z : E × ℝ => H ((z.1,ω),z.2)) (μ.prod (ν ω).totalVariation) := by
      apply (integrable_prod_iff hmω.aestronglyMeasurable).mpr
      refine ⟨hiω,?_⟩
      simpa only [Real.norm_eq_abs,V] using hvω
    exact ⟨hiω',(signed_integral_fubini μ (ν ω) _ hiω').2.2⟩

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.stieltjes_fubini_absolute_integrability

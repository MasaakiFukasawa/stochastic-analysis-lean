import Chapter2StieltjesFubiniAbsolute
import Chapter2RandomSignedIntegral
import Chapter2L1BochnerPointwise

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal Classical
namespace Asakura.Chapter2Complete
open Asakura.FullAudit
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

/-- The L1-valued covariance integral equals the ordinary signed Stieltjes
integral of the averaged integrand. Absolute integrability and all random
integral measurability are derived from the interval KW bound. -/
theorem signed_bochner_fubini_of_energy
    {E Ω : Type*} [MeasurableSpace E] [MeasurableSpace Ω]
    (μ : Measure E) [SigmaFinite μ] (P : Measure Ω) [IsProbabilityMeasure P]
    (α β : Ω → Measure ℝ) [∀ ω, IsFiniteMeasure (α ω)] [∀ ω, IsFiniteMeasure (β ω)]
    (ν : Ω → SignedMeasure ℝ) (hv : Measurable (fun ω => (ν ω).totalVariation))
    (hm : ∀ s t, Measurable (fun ω => ν ω (Ioc s t)))
    (hc : ∀ᵐ ω ∂P, ∀ s t, s ≤ t → |ν ω (Ioc s t)| ≤
      Real.sqrt ((α ω).real (Ioc s t))*Real.sqrt ((β ω).real (Ioc s t)))
    (H : (E × Ω) × ℝ → ℝ) (hH : Measurable H)
    (hi : ∀ᵐ x ∂μ, ∀ᵐ ω ∂P, Integrable (fun r => H ((x,ω),r)^2) (α ω))
    (hAi : ∀ᵐ x ∂μ, Integrable (fun ω => ∫ r, H ((x,ω),r)^2 ∂α ω) P)
    (hBi : Integrable (fun ω => (β ω).real univ) P)
    (hN : Integrable (fun x => Real.sqrt (∫ ω, ∫ r, H ((x,ω),r)^2 ∂α ω ∂P)) μ)
    (Z : E → Lp ℝ 1 P) (hZ : Integrable Z μ)
    (he : ∀ᵐ x ∂μ, (Z x : Ω → ℝ) =ᵐ[P]
      (fun ω => signedIntegralRaw (ν ω) (fun r => H ((x,ω),r)))) :
    ((∫ x, Z x ∂μ : Lp ℝ 1 P) : Ω → ℝ) =ᵐ[P]
      (fun ω => signedIntegralRaw (ν ω) (fun r => ∫ x, H ((x,ω),r) ∂μ)) := by
  obtain ⟨hVi,_,hfi⟩ := stieltjes_fubini_absolute_integrability μ P α β ν hv hc H hH hi hAi hBi hN
  let g := fun z : E × Ω => signedIntegralRaw (ν z.2) (fun r => H (z,r))
  have hgm : Measurable g := random_signed_integral_measurable (fun z : E × Ω => ν z.2)
    (hv.comp measurable_snd) (fun s t => (hm s t).comp measurable_snd) H hH
  let κ : Kernel (E × Ω) ℝ := ⟨fun z => (ν z.2).totalVariation,hv.comp measurable_snd⟩
  have hκ z : IsFiniteMeasure (κ z) := show IsFiniteMeasure (ν z.2).totalVariation from inferInstance
  have hpath : ∀ᵐ z ∂μ.prod P, Integrable (fun r => H (z,r)) (ν z.2).totalVariation := by
    apply (Measure.ae_prod_iff_ae_ae (finite_kernel_integrable_set_measurable κ hκ H hH)).mpr
    filter_upwards [hi] with x hix
    filter_upwards [hix,hc] with ω hiω hcω
    exact (signed_stieltjes_absolute_integral_bound (α ω) (β ω) (ν ω) hcω _
      (hH.comp measurable_prodMk_left) hiω).1
  have hgi : Integrable g (μ.prod P) := hVi.mono' hgm.aestronglyMeasurable
    (hpath.mono (fun z hz => by
      simpa only [Real.norm_eq_abs] using signed_integral_absolute_bound (ν z.2) _ hz))
  have hb := l1_bochner_integral_pointwise μ P Z hZ g hgi he
  filter_upwards [hb,hfi] with ω hω hfω
  exact hω.trans hfω.2

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.signed_bochner_fubini_of_energy

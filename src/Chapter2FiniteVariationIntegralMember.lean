import Chapter2FiniteTimeProjection
import Chapter2RightContinuousIntegralJordan
import Chapter2StieltjesRestriction

open MeasureTheory Set Filter
open scoped Topology ENNReal Classical
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

/-- A genuine finite-horizon Stieltjes integral belongs to the manuscript's
A, with adapted right-continuous increasing parts, even when the integrator
has jumps. The endpoint is extended constantly on the original time space. -/
theorem finite_stieltjes_integral_member
    {Ω : Type*} {T : EReal} [Fact (0 ≤ T)]
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F)
    (d : ℝ) (hd : 0 ≤ d) (hdT : (d:EReal) ≤ T)
    (A : Ω → ℝ → ℝ) (hA : ∀ ω, MonotoneOn (A ω) (Icc 0 d))
    (hr : ∀ ω r, r ∈ Icc 0 d → ContinuousWithinAt (A ω) (Icc 0 d ∩ Ici r) r)
    (hm : ∀ r : Icc (0:ℝ) d, Measurable[F (realTimeClamp r.val)] (fun ω => A ω r.val))
    (H : Ω × ℝ → ℝ)
    (hH : @Measurable _ _
      (progressiveSpace (fun t : Icc (0:ℝ) d => F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) d => H (z.1,z.2.val)))
    (hi : ∀ ω, Integrable (fun r => H (ω,r)) (intervalStieltjes 0 d hd (A ω) (hA ω) (hr ω)).measure) :
    AdaptedVariationWitness F (fun t ω => ∫ r in Iic (finitePrefixTime d hd t).val,
      H (ω,r) ∂(intervalStieltjes 0 d hd (A ω) (hA ω) (hr ω)).measure) := by
  have he ω : (fun r => H (ω,(projIcc 0 d hd r).val)) =ᵐ[
      (intervalStieltjes 0 d hd (A ω) (hA ω) (hr ω)).measure] (fun r => H (ω,r)) := by
    filter_upwards [interval_stieltjes_ae_mem_Ioc 0 d hd (A ω) (hA ω) (hr ω)] with r hr'
    rw [projIcc_of_mem hd ⟨hr'.1.le,hr'.2⟩]
  obtain ⟨U,V,hmon,hUVr,hUVm,hUV⟩ := right_continuous_stieltjes_integral_jordan 0 d hd
    (fun t : Icc (0:ℝ) d => F (realTimeClamp t.val))
    (fun s t hst => hF (real_time_clamp_mono hst)) A hA hr hm _ hH
    (fun ω => (hi ω).congr (he ω).symm)
  have hb := adapted_variation_of_finite_interval_parts F hF d hd hdT U V hUVm hmon hUVr
  have heq : (fun (t : ClosedTime T) ω => ∫ r in Iic (finitePrefixTime d hd t).val,
      H (ω,r) ∂(intervalStieltjes 0 d hd (A ω) (hA ω) (hr ω)).measure) =
      (fun t ω => U ω (finitePrefixTime d hd t).val-V ω (finitePrefixTime d hd t).val) := by
    funext t ω
    rw [← hUV ω (finitePrefixTime d hd t).val]
    exact integral_congr_ae (ae_restrict_of_ae (he ω).symm)
  rw [heq]
  exact hb

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.finite_stieltjes_integral_member

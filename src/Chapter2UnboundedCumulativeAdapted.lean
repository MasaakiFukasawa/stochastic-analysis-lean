import Chapter2CumulativeAdapted
import Chapter2FiniteKernelIntegral

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

/-- Adaptedness for right-continuous increasing integrators, with no bound
on the random Stieltjes mass. -/
theorem cumulative_stieltjes_adapted_without_mass_bound
    {Ω : Type*} (a b : ℝ) (hab : a ≤ b)
    (F : Icc a b → MeasurableSpace Ω) (hF : Monotone F)
    (A : Ω → ℝ → ℝ)
    (hA : ∀ ω, MonotoneOn (A ω) (Icc a b))
    (hr : ∀ ω x, x ∈ Icc a b → ContinuousWithinAt (A ω) (Icc a b ∩ Ici x) x)
    (hm : ∀ r : Icc a b, @Measurable _ _ (F r) inferInstance (fun ω => A ω r.val))
    (H : Ω × Icc a b → ℝ)
    (hH : @Measurable _ _ (progressiveSpace F) inferInstance H)
    (t : Icc a b) :
    @Measurable _ _ (F t) inferInstance
      (fun ω => ∫ r in Iic t.val, H (ω,projIcc a b hab r)
        ∂(intervalStieltjes a b hab (A ω) (hA ω) (hr ω)).measure) := by
  letI : MeasurableSpace Ω := F t
  have hAt (ω) : MonotoneOn (A ω) (Icc a t.val) :=
    (hA ω).mono (fun x hx => ⟨hx.1,hx.2.trans t.property.2⟩)
  have hrt (ω x) (hx : x ∈ Icc a t.val) :
      ContinuousWithinAt (A ω) (Icc a t.val ∩ Ici x) x :=
    (hr ω x ⟨hx.1,hx.2.trans t.property.2⟩).mono
      (fun y hy => ⟨⟨hy.1.1,hy.1.2.trans t.property.2⟩,hy.2⟩)
  have hmt (r) (hr : r ∈ Icc a t.val) : Measurable (fun ω => A ω r) :=
    (hm ⟨r,hr.1,hr.2.trans t.property.2⟩).mono (hF hr.2) le_rfl
  let κ : Kernel Ω ℝ := {
    toFun := fun ω => (intervalStieltjes a t.val t.property.1 (A ω) (hAt ω) (hrt ω)).measure
    measurable' := random_stieltjes_measure_measurable_on a t.val t.property.1 A hAt hrt hmt }
  have hp := progressive_clamped_measurable a b hab F H hH t
  have hi := finite_kernel_integral_measurable κ
    (fun ω => intervalStieltjes_finite a t.val t.property.1 (A ω) (hAt ω) (hrt ω)) _ hp
  have he (ω) : (∫ r, H (ω,projIcc a b hab (intervalClamp a t.val t.property.1 r)) ∂κ ω) =
      ∫ r in Iic t.val, H (ω,projIcc a b hab r)
        ∂(intervalStieltjes a b hab (A ω) (hA ω) (hr ω)).measure := by
    have hk : κ ω = (intervalStieltjes a b hab (A ω) (hA ω) (hr ω)).measure.restrict (Iic t.val) :=
      interval_stieltjes_restrict_Iic a b t.val t.property.1 t.property.2 (A ω)
        (hA ω) (hr ω) (hAt ω) (hrt ω)
    rw [← hk]
    apply integral_congr_ae
    filter_upwards [interval_stieltjes_ae_mem_Ioc a t.val t.property.1 (A ω) (hAt ω) (hrt ω)] with r hr
    rw [intervalClamp_eq a t.val t.property.1 ⟨hr.1.le,hr.2⟩]
  simpa only [he] using hi

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.cumulative_stieltjes_adapted_without_mass_bound

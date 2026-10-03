import Chapter2StieltjesRestriction
import Chapter2ProgressiveSpace
import Mathlib.Probability.Kernel.MeasurableIntegral

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/-- Progressive measurability gives joint measurability after clamping time
at a fixed observation time. -/
theorem progressive_clamped_measurable
    {Ω : Type*} (a b : ℝ) (hab : a ≤ b)
    (F : Icc a b → MeasurableSpace Ω) (H : Ω × Icc a b → ℝ)
    (hH : @Measurable _ _ (progressiveSpace F) inferInstance H)
    (t : Icc a b) :
    @Measurable _ _ ((F t).prod inferInstance) inferInstance
      (fun p : Ω × ℝ => H (p.1, projIcc a b hab (intervalClamp a t.val t.property.1 p.2))) := by
  letI : MeasurableSpace Ω := F t
  let u : ℝ → Icc a b := fun r => projIcc a b hab (intervalClamp a t.val t.property.1 r)
  have hu (r) : u r ≤ t := by
    have hc := intervalClamp_mem a t.val t.property.1 r
    change (projIcc a b hab (intervalClamp a t.val t.property.1 r) : ℝ) ≤ t.val
    rw [projIcc_of_mem hab ⟨hc.1,hc.2.trans t.property.2⟩]
    exact hc.2
  have hm : Measurable u := continuous_projIcc.measurable.comp
    (intervalClamp_continuous a t.val t.property.1).measurable
  have hg : Measurable (fun p : Ω × ℝ => (p.1, (⟨u p.2,hu p.2⟩ : Iic t))) :=
    measurable_fst.prodMk (hm.comp measurable_snd).subtype_mk
  exact ((measurable_progressive_iff F H).1 hH t).comp hg

/-- Integrating a progressive integrand against an adapted increasing
continuous-from-the-right path gives an adapted cumulative integral. -/
theorem cumulative_stieltjes_adapted
    {Ω : Type*} (a b : ℝ) (hab : a ≤ b)
    (F : Icc a b → MeasurableSpace Ω) (hF : Monotone F)
    (A : Ω → ℝ → ℝ)
    (hA : ∀ ω, MonotoneOn (A ω) (Icc a b))
    (hr : ∀ ω x, x ∈ Icc a b → ContinuousWithinAt (A ω) (Icc a b ∩ Ici x) x)
    (hm : ∀ r : Icc a b, @Measurable _ _ (F r) inferInstance (fun ω => A ω r.val))
    (K : ℝ) (hK : ∀ ω, A ω b-A ω a ≤ K)
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
  letI : IsFiniteKernel κ := ⟨ENNReal.ofReal K, ENNReal.ofReal_lt_top, fun ω => by
    change (intervalStieltjes a t.val t.property.1 (A ω) (hAt ω) (hrt ω)).measure univ ≤ _
    rw [interval_stieltjes_total_mass a t.val t.property.1 A hAt hrt]
    apply ENNReal.ofReal_le_ofReal
    exact (sub_le_sub_right (hA ω t.property (right_mem_Icc.2 hab) t.property.2) _).trans (hK ω)⟩
  have hp := progressive_clamped_measurable a b hab F H hH t
  have hi := hp.stronglyMeasurable.integral_kernel_prod_right' (κ := κ)
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
  simpa only [he] using hi.measurable

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.progressive_clamped_measurable

#print axioms Asakura.Chapter2Complete.cumulative_stieltjes_adapted

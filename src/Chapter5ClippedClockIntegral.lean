import Chapter5ClockSemimartingale
import Chapter4ClockVariationIntegral

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4

theorem clipped_clock_variation_integral
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {T : EReal} [Fact (0 ≤ T)]
    (R : ℝ) (hR : 0 ≤ R) (hRT : (R:EReal) ≤ T)
    (I : ClosedTime T → Ω → ℝ) (H : Ω × ℝ → ℝ)
    (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n) (hcT : ∀ n, (c n:EReal) < T)
    (hcc : ∀ t, t < ⊤ → ∃ n, t < realTimeClamp (T := T) (c n))
    (hI : VariationIntegralFormula P c hc
      (fun t _ => (finitePrefixTime (T := T) R hR t).val) H I)
    (d : ℝ) (hd : 0 ≤ d) (hdR : d ≤ R) (hdT : (d:EReal) < T) :
    I (realTimeClamp d) =ᵐ[P] fun w => ∫ r in 0..d, H (w,r) := by
  let A := fun t (_ : Ω) => (finitePrefixTime (T := T) R hR t).val
  have hmono : ∀ w, Monotone (fun r : ℝ => A (realTimeClamp r) w) := by
    intro w s t hst
    exact finite_prefix_time_mono R hR (real_time_clamp_mono hst)
  have hcont : ∀ w, Continuous (fun r : ℝ => A (realTimeClamp r) w) := by
    intro w
    exact continuous_subtype_val.comp ((finite_prefix_time_continuous R hR).comp real_time_clamp_continuous)
  have hdt : realTimeClamp (T := T) d < ⊤ := by
    change (realTimeClamp d : EReal) < T
    rw [real_time_clamp_eq d hd hdT.le]; exact hdT
  obtain ⟨j,hj⟩ := hcc _ hdt
  have hdc : d ≤ c j := by
    change (realTimeClamp d : EReal) < (realTimeClamp (c j) : EReal) at hj
    rw [real_time_clamp_eq d hd hdT.le,real_time_clamp_eq (c j) (hc j) (hcT j).le] at hj
    exact EReal.coe_le_coe_iff.mp hj.le
  have he := positive_variation_integral_at_time P A I H c hc hcT
    (fun _ w => (hmono w).monotoneOn _) (fun _ w => (hcont w).continuousOn) hI
    j d hd hdc (fun w => (hmono w).monotoneOn _) (fun w => (hcont w).continuousOn)
  filter_upwards [he] with w hw
  rw [hw]
  have hmeasure : intervalStieltjes 0 d hd (fun r => A (realTimeClamp r) w)
      ((hmono w).monotoneOn _) (fun r hr => ((hcont w).continuousOn r hr).mono inter_subset_left) =
      intervalStieltjes 0 d hd id (monotone_id.monotoneOn _)
        (fun _ _ => continuous_id.continuousWithinAt) := by
    apply StieltjesFunction.ext
    intro r
    exact finite_prefix_time_of_real R _ hR
      (Icc_subset_Icc_right hdR (intervalClamp_mem 0 d hd r)) hRT
  rw [hmeasure,clock_stieltjes_integral]

end Asakura.Chapter5

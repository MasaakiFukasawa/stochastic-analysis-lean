import Chapter3PartitionStepProgressive
import Chapter3PolarizedStieltjesMeasure

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

/-- The step error has exactly the Stieltjes energy bound used in the
Karandikar approximation. The possible discrepancy at t=0 is harmless
because the constructed measure is carried by (0,d]. -/
theorem partition_step_stieltjes_error_energy
    {T : EReal} [Fact (0 ≤ T)] (d : ℝ) (hd : 0 ≤ d) (hdT : (d:EReal) < T)
    (H : ClosedTime T → ℝ) (hH : ∀ t, t < ⊤ → ContinuousAt H t)
    (A : ℝ → ℝ) (hA : MonotoneOn A (Icc 0 d))
    (hrA : ∀ x, x ∈ Icc 0 d → ContinuousWithinAt A (Icc 0 d ∩ Ici x) x)
    (τ : ℕ → ClosedTime T) (hτ : Monotone τ) (h0 : τ 0 = ⊥)
    (hco : ∀ t, t < ⊤ → ∃ N, t < τ N) (δ : ℝ) (hδ : 0 ≤ δ)
    (hosc : ∀ j t, τ j ≤ t → t ≤ τ (j+1) → |H (τ j)-H t| ≤ δ) :
    let μ := (intervalStieltjes 0 d hd A hA hrA).measure
    let E := fun r => (H (realTimeClamp r)-partitionStep H τ (realTimeClamp r))^2
    Integrable E μ ∧ (∫ r, E r ∂μ) ≤ δ^2*(A d-A 0) := by
  intro μ E
  letI : IsFiniteMeasure μ := intervalStieltjes_finite 0 d hd A hA hrA
  have hmH := (continuous_weight_stieltjes_integrable d hd hdT H hH A hA hrA).aestronglyMeasurable
  have hmS : AEStronglyMeasurable (fun r => partitionStep H τ (realTimeClamp r)) μ :=
    ((partition_step_measurable H τ).comp real_time_clamp_continuous.measurable).aestronglyMeasurable
  have hmE : AEStronglyMeasurable E μ := by
    convert (hmH.sub hmS).pow 2 using 1
  have hb : ∀ᵐ r ∂μ, |E r| ≤ δ^2 := by
    filter_upwards [interval_stieltjes_ae_mem_Ioc 0 d hd A hA hrA] with r hr
    have hrt : realTimeClamp (T := T) r < ⊤ := by
      change (realTimeClamp r : EReal) < T
      rw [real_time_clamp_eq r hr.1.le ((EReal.coe_le_coe hr.2).trans hdT.le)]
      exact (EReal.coe_le_coe hr.2).trans_lt hdT
    have hr0 : (⊥ : ClosedTime T) < realTimeClamp r := by
      change (0:EReal) < (realTimeClamp r : EReal)
      rw [real_time_clamp_eq r hr.1.le ((EReal.coe_le_coe hr.2).trans hdT.le)]
      exact_mod_cast hr.1
    have he := partition_step_error H τ hτ h0 hco δ hosc (realTimeClamp r) hr0 hrt
    have he' : |H (realTimeClamp r)-partitionStep H τ (realTimeClamp r)| ≤ δ := by
      simpa only [abs_sub_comm] using he
    have hp := pow_le_pow_left₀ (abs_nonneg _) he' 2
    simpa only [E,abs_pow] using hp
  have hi : Integrable E μ := (integrable_const (δ^2)).mono' hmE
    (by simpa only [Real.norm_eq_abs] using hb)
  refine ⟨hi,?_⟩
  have he : (∫ r, E r ∂μ) ≤ ∫ _, δ^2 ∂μ :=
    integral_mono_ae hi (integrable_const _) (hb.mono (fun r hr => (le_abs_self _).trans hr))
  have hmass : μ.real univ = A d-A 0 := by
    rw [Measure.real,interval_stieltjes_total_mass 0 d hd (fun _ : Unit => A)
      (fun _ => hA) (fun _ => hrA) ()]
    exact ENNReal.toReal_ofReal (sub_nonneg.mpr (hA (left_mem_Icc.mpr hd) (right_mem_Icc.mpr hd) hd))
  simpa only [integral_const,smul_eq_mul,hmass,mul_comm] using he

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.partition_step_stieltjes_error_energy

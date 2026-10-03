import Chapter4ProgressiveItoBDG
import Chapter4FiniteRunningMaximum

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter4
set_option maxHeartbeats 1600000

/-- Convert the extended-moment BDG bound to an actual finite p-th moment.
This proves the required integrability instead of assuming it. -/
theorem power_moment_of_lintegral_bound
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    (P : Measure Ω) (Y : Ω → E) (hm : AEStronglyMeasurable Y P)
    (p : ℝ) (hp : 0<p) (V : Ω → ℝ) (hv : Integrable V P) (hvp : ∀ w,0≤V w)
    (C : ℝ) (hC : 0≤C)
    (hb : (∫⁻ w,(ENNReal.ofReal ‖Y w‖)^p ∂P)≤ENNReal.ofReal C*(∫⁻ w,ENNReal.ofReal (V w) ∂P)) :
    MemLp Y (ENNReal.ofReal p) P ∧ (∫ w,‖Y w‖^p ∂P)≤C*(∫ w,V w ∂P) := by
  have hpos : ∀ᵐ w ∂P,0≤‖Y w‖^p := .of_forall (fun w => Real.rpow_nonneg (norm_nonneg _) _)
  have hbound : (∫⁻ w,ENNReal.ofReal (‖Y w‖^p) ∂P)≤ENNReal.ofReal (C*(∫ w,V w ∂P)) := by
    simp_rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp.le]
    rw [ENNReal.ofReal_mul hC,ofReal_integral_eq_lintegral_ofReal hv (.of_forall hvp)]
    exact hb
  have hi : Integrable (fun w => ‖Y w‖^p) P :=
    ⟨(Real.continuous_rpow_const hp.le).comp_aestronglyMeasurable hm.norm,
      (hasFiniteIntegral_iff_ofReal hpos).2 (hbound.trans_lt ENNReal.ofReal_lt_top)⟩
  have hiY : MemLp Y (ENNReal.ofReal p) P := by
    apply (integrable_norm_rpow_iff hm (ne_of_gt (ENNReal.ofReal_pos.mpr hp)) ENNReal.ofReal_ne_top).mp
    simpa only [ENNReal.toReal_ofReal hp.le] using hi
  rw [← ofReal_integral_eq_lintegral_ofReal hi hpos] at hbound
  exact ⟨hiY,(ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC (integral_nonneg hvp))).mp hbound⟩

end Asakura.Chapter4

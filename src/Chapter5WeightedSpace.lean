import Chapter2ProgressiveEnergyComplete
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Chapter5EnergyEstimates

open MeasureTheory Set
open scoped ENNReal
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter2Written Asakura.Chapter2Complete

noncomputable def exponentialEnergyMeasure {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure (Ω × ℝ)) (β : ℝ) : Measure (Ω × ℝ) :=
  ν.withDensity (fun z => ENNReal.ofReal (Real.exp (β*z.2)))

/-- The weighted progressive space used for the BSDE contraction is
complete for the actual exponential energy measure. -/
theorem weighted_progressive_complete {Ω : Type*} [MeasurableSpace Ω]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (c : ℕ → ℝ) (ν : Measure (Ω × ℝ)) (β : ℝ) :
    CompleteSpace (progressiveEnergyRange F c (exponentialEnergyMeasure ν β)) :=
  progressive_energy_complete F c _

/-- Its squared norm is precisely the manuscript's weighted integral. -/
theorem weighted_L2_norm_sq {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure (Ω × ℝ)) (β : ℝ)
    (H : Lp ℝ 2 (exponentialEnergyMeasure ν β)) :
    ‖H‖^2 = ∫ z, Real.exp (β*z.2) * H z^2 ∂ν := by
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  simp only [real_inner_self_eq_norm_sq,Real.norm_eq_abs,sq_abs]
  change (∫ z, H z^2 ∂ν.withDensity (fun z => ENNReal.ofReal (Real.exp (β*z.2)))) = _
  rw [integral_withDensity_eq_integral_toReal_smul]
  · simp only [ENNReal.toReal_ofReal (Real.exp_pos _).le,smul_eq_mul]
  · exact (Real.continuous_exp.measurable.comp (measurable_const.mul measurable_snd)).ennreal_ofReal
  · exact ae_of_all _ fun _ => ENNReal.ofReal_lt_top

end Asakura.Chapter5

import Chapter3BDGConstants

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

/-- The extended p-moment expression of the norm, without an Lp membership assumption. -/
theorem nonnegative_eLpNorm_moment
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (S : Ω → ℝ) (hS : Measurable S) (hSp : ∀ ω, 0 ≤ S ω) (p : ℝ) (hp : 0 < p) :
    eLpNorm S (ENNReal.ofReal p) P = (∫⁻ ω, (ENNReal.ofReal (S ω))^p ∂P)^(1/p) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simp [hp]) (by simp) hS.aestronglyMeasurable]
  simp only [ENNReal.toReal_ofReal hp.le,← ofReal_norm,Real.norm_eq_abs,abs_of_nonneg (hSp _)]

/-- The bracket moment is the pth moment of its square root. -/
theorem sqrt_eLpNorm_moment
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (A : Ω → ℝ) (hA : Measurable A) (hAp : ∀ ω, 0 ≤ A ω) (p : ℝ) (hp : 0 < p) :
    eLpNorm (fun ω => Real.sqrt (A ω)) (ENNReal.ofReal p) P =
      (∫⁻ ω, (ENNReal.ofReal (A ω))^(p/2) ∂P)^(1/p) := by
  rw [nonnegative_eLpNorm_moment P (fun ω => Real.sqrt (A ω)) (Real.continuous_sqrt.measurable.comp hA)
    (fun ω => Real.sqrt_nonneg _) p hp]
  congr 1
  apply lintegral_congr
  intro ω
  rw [Real.sqrt_eq_rpow,← ENNReal.ofReal_rpow_of_nonneg (hAp ω) (by norm_num),← ENNReal.rpow_mul]
  congr 1
  ring

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.nonnegative_eLpNorm_moment
#print axioms Asakura.Chapter3Complete.sqrt_eLpNorm_moment

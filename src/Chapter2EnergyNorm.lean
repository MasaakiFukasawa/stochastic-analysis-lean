import Chapter2StoppedEnergy
import FullAuditMartingalePathNorm

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 600000

/-- The scalar L2 seminorm in terms of the square integral. -/
theorem real_eLpNorm_two_energy
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (f : Ω → ℝ) (hf : MemLp f 2 P) :
    eLpNorm f 2 P = (ENNReal.ofReal (∫ ω, f ω ^ 2 ∂P)) ^ (1/(2:ℝ)) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hf.aestronglyMeasurable]
  have hi := (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).1 hf
  have hn : 0 ≤ᵐ[P] (fun ω => f ω ^ 2) := .of_forall fun ω => sq_nonneg _
  rw [ofReal_integral_eq_lintegral_ofReal hi hn]
  norm_num only [ENNReal.toReal_ofNat,ENNReal.rpow_two]
  congr 2
  funext ω
  rw [← ofReal_norm,Real.norm_eq_abs,← ENNReal.ofReal_pow (abs_nonneg _),sq_abs]

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.real_eLpNorm_two_energy

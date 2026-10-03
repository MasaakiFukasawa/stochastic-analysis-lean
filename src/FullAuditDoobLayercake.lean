import FullAuditDoobWeak
import Mathlib.Analysis.SpecialFunctions.Pow.Integral

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.FullAudit

/-- Integrating the weak tail estimate with weight t^(p-2). The second measure
will be Y dP, so the second layer-cake identity is the manuscript's Tonelli step. -/
theorem doob_layercake_two_measures {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) (S : Ω → ℝ) (hS : Measurable S) (hpos : ∀ ω, 0 ≤ S ω)
    (p : ℝ) (hp : 1 < p)
    (htail : ∀ t > 0, ENNReal.ofReal t * μ {ω | t ≤ S ω} ≤ ν {ω | t ≤ S ω}) :
    ∫⁻ ω, ENNReal.ofReal (S ω ^ p) ∂μ ≤
      ENNReal.ofReal (p/(p-1)) * ∫⁻ ω, ENNReal.ofReal (S ω ^ (p-1)) ∂ν := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hp1 : 0 < p-1 := sub_pos.mpr hp
  rw [lintegral_rpow_eq_lintegral_meas_le_mul μ (Eventually.of_forall hpos) hS.aemeasurable hp0,
    lintegral_rpow_eq_lintegral_meas_le_mul ν (Eventually.of_forall hpos) hS.aemeasurable hp1]
  have hc : ENNReal.ofReal (p/(p-1)) * ENNReal.ofReal (p-1) = ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_mul (div_nonneg hp0.le hp1.le), div_mul_cancel₀ _ hp1.ne']
  rw [← mul_assoc,hc]
  gcongr 1
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : 0 < t := ht
  have hpow : t ^ (p-1) = t * t ^ (p-1-1) := by
    calc
      _ = t ^ (1 + (p-1-1)) := by congr 1; ring
      _ = t ^ (1:ℝ) * t ^ (p-1-1) := Real.rpow_add ht0 _ _
      _ = _ := by rw [Real.rpow_one]
  rw [hpow, ENNReal.ofReal_mul ht0.le]
  calc
    μ {ω | t ≤ S ω} * (ENNReal.ofReal t * ENNReal.ofReal (t ^ (p-1-1))) =
        (ENNReal.ofReal t * μ {ω | t ≤ S ω}) * ENNReal.ofReal (t ^ (p-1-1)) := by ac_rfl
    _ ≤ _ := by gcongr; exact htail t ht0

end Asakura.FullAudit

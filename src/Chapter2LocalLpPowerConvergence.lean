import Chapter2LocalLpExhaustion
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

theorem finite_lp_norm_power {S : Type*} [MeasurableSpace S]
    (μ : Measure S) (p : ℝ≥0∞) (hp : 0 < p.toReal) (f : S → ℝ) (hf : MemLp f p μ) :
    (eLpNorm f p μ).toReal ^ p.toReal = ∫ x, |f x| ^ p.toReal ∂μ := by
  have hp0 : p ≠ 0 := by intro h; simp [h] at hp
  have hpt : p ≠ ∞ := by intro h; simp [h] at hp
  rw [hf.eLpNorm_eq_integral_rpow_norm hp0 hpt,ENNReal.toReal_ofReal (by positivity)]
  rw [Real.rpow_inv_rpow (integral_nonneg (fun x => by positivity)) hp.ne']
  simp only [Real.norm_eq_abs]

theorem finite_lp_convergence_power_iff {S : Type*} [MeasurableSpace S]
    (μ : Measure S) (p : ℝ≥0∞) (hp : 0 < p.toReal)
    (f : ℕ → S → ℝ) (hf : ∀ n, MemLp (f n) p μ) :
    Tendsto (fun n => (eLpNorm (f n) p μ).toReal) atTop (𝓝 0) ↔
      Tendsto (fun n => ∫ x, |f n x| ^ p.toReal ∂μ) atTop (𝓝 0) := by
  constructor
  · intro h
    have hh := h.rpow_const (p := p.toReal) (Or.inr hp.le)
    simpa only [Real.zero_rpow hp.ne',finite_lp_norm_power μ p hp _ (hf _)] using hh
  · intro h
    have hh := h.rpow_const (p := p.toReal⁻¹) (Or.inr (inv_nonneg.mpr hp.le))
    have he n : (∫ x, |f n x| ^ p.toReal ∂μ) ^ p.toReal⁻¹ = (eLpNorm (f n) p μ).toReal := by
      rw [← finite_lp_norm_power μ p hp _ (hf n),Real.rpow_rpow_inv ENNReal.toReal_nonneg hp.ne']
    simpa only [he,Real.zero_rpow (inv_ne_zero hp.ne')] using hh

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.finite_lp_convergence_power_iff

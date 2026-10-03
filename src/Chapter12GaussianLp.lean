import FullAuditCylinderCoordinates
import Mathlib.MeasureTheory.Function.Holder

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
namespace Asakura.Chapter12
open Asakura.FullAudit
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 300000

/-- Polynomial cylinder growth gives every finite Lp norm required on the
right of Gaussian integration by parts, not just integrability. -/
theorem polynomial_growth_gaussian_memLp {ι : Type*} [Fintype ι]
    {f : (ι → ℝ) → ℝ} (hm : Measurable f) (hf : PolyGrowth f)
    (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp f p (Measure.pi fun _ => gaussianReal 0 1) := by
  obtain ⟨C,hC,k,hf⟩ := hf
  let μ : Measure (ι → ℝ) := Measure.pi fun _ => gaussianReal 0 1
  by_cases hk : k = 0
  · subst k
    exact MemLp.of_bound hm.aestronglyMeasurable C
      (ae_of_all _ fun z => by simpa only [pow_zero,mul_one,Real.norm_eq_abs] using hf z)
  have hkt : (k : ℝ≥0∞) ≠ ∞ := by simp
  have hk0 : (k : ℝ≥0∞) ≠ 0 := by exact_mod_cast hk
  have hn : MemLp (fun z : ι → ℝ => ‖z‖) (p*k) μ :=
    (finite_gaussian_all_moments (ι := ι) (p*k) (ENNReal.mul_ne_top hp hkt)).norm
  have hb : MemLp (fun z : ι → ℝ => 1+‖z‖) (p*k) μ := (memLp_const (μ := μ) (p := p*k) (1 : ℝ)).add hn
  have hpow : MemLp (fun z : ι → ℝ => (1+‖z‖)^k) p μ := by
    have h := hb.norm_rpow_div (k : ℝ≥0∞)
    have hnrm (z : ι → ℝ) : ‖1+‖z‖‖ = 1+‖z‖ := by
      rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    simpa only [hnrm,ENNReal.toReal_natCast,Real.rpow_natCast,
      ENNReal.mul_div_cancel_right hk0 hkt] using h
  apply (hpow.const_mul C).mono' hm.aestronglyMeasurable
  exact ae_of_all _ fun z => by simpa only [Real.norm_eq_abs] using hf z

end Asakura.Chapter12

import Appendix
import Mathlib.MeasureTheory.Measure.WithDensity
open MeasureTheory Set
open scoped ENNReal
namespace Asakura

/-- A.3: the manuscript's finite-fibre formula really defines a measure. -/
theorem simple_integral_defines_measure {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : SimpleFunc Ω ℝ≥0∞) :
    ∃ ν : Measure Ω, ∀ A, MeasurableSet A →
      ν A = ∑ y ∈ f.range, y * μ (f ⁻¹' {y} ∩ A) := by
  refine ⟨μ.withDensity f, fun A hA => ?_⟩
  rw [withDensity_apply f hA, f.lintegral_eq_lintegral]
  exact f.lintegral_restrict A μ

/-- A.3: monotonicity at the finite-simple-function level. -/
theorem simple_integral_mono {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f g : SimpleFunc Ω ℝ≥0∞) (h : f ≤ g) :
    f.lintegral μ ≤ g.lintegral μ := SimpleFunc.lintegral_mono_fun h

/-- A.3: additivity at the finite-simple-function level. -/
theorem simple_integral_add {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f g : SimpleFunc Ω ℝ≥0∞) :
    (f + g).lintegral μ = f.lintegral μ + g.lintegral μ := by
  rw [← (f + g).lintegral_eq_lintegral, ← f.lintegral_eq_lintegral,
    ← g.lintegral_eq_lintegral]
  exact lintegral_add_left f.measurable g

/-- A.2: the original nonnegative extended-real monotone measurability lemma. -/
theorem monotone_ennreal_measurable {f : ℝ≥0∞ → ℝ≥0∞} (hf : Monotone f) :
    Measurable f := hf.measurable

/-- B.1: the seminorm vanishes precisely on the a.e. zero class, including infinity. -/
theorem lp_zero_iff {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    (μ : Measure Ω) (p : ℝ≥0∞) (hp : p ≠ 0) (f : Ω → E) :
    eLpNorm f p μ = 0 ↔ f =ᵐ[μ] 0 := eLpNorm_eq_zero_iff hp

/-- B.1: the endpoint Holder inequality, p=1 and q=infinity. -/
theorem holder_endpoint {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f g : Ω → ℝ) :
    eLpNorm (fun x => f x * g x) 1 μ ≤ eLpNorm f 1 μ * eLpNorm g ⊤ μ := by
  simpa only [Pi.smul_def, smul_eq_mul] using!
    (eLpNorm_smul_le_eLpNorm_mul_eLpNorm_top_of_pos (μ := μ) (φ := f) (f := g)
      (1 : ℝ≥0∞) (by norm_num))
end Asakura

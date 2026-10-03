import FullAuditTestMeasure
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.Probability.Distributions.Gaussian.Real

open MeasureTheory ProbabilityTheory Set
open scoped NNReal
namespace Asakura.Chapter4
set_option backward.isDefEq.respectTransparency false

/-- The probabilistic inference in the Levy-characterization exercise:
a conditional characteristic function identifies the Gaussian increment law
and its independence of the entire conditioning sigma algebra. The preceding
Ito calculation of this conditional characteristic function remains separate. -/
theorem gaussian_independent_of_conditional_characteristic
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (G : MeasurableSpace Ω) (hG : G ≤ m) (X : Ω → ℝ) (hX : Measurable[m] X)
    (v : ℝ≥0)
    (h : ∀ u : ℝ, P[(fun ω => Complex.exp ((u:ℂ)*(X ω:ℂ)*Complex.I)) | G] =ᵐ[P]
      (fun _ => Complex.exp (-(v:ℂ)*(u:ℂ)^2/2))) :
    HasLaw X (gaussianReal 0 v) P ∧
      Indep (MeasurableSpace.comap X inferInstance) G P := by
  apply Asakura.FullAudit.independent_law_of_restricted_laws G P (gaussianReal 0 v) hG X hX
  intro A hA
  letI : IsFiniteMeasure (P A • gaussianReal 0 v) := ⟨by simp [Measure.smul_apply,measure_lt_top]⟩
  apply Measure.ext_of_charFun
  funext u
  let f : Ω → ℂ := fun ω => Complex.exp ((u:ℂ)*(X ω:ℂ)*Complex.I)
  have hf : Integrable f P := by
    apply Integrable.of_bound (by dsimp [f]; fun_prop) 1
    apply ae_of_all
    intro ω
    simp [f, Complex.norm_exp]
  rw [charFun_apply_real, integral_map hX.aemeasurable (by fun_prop),
    charFun_apply_real, integral_smul_measure]
  change (∫ ω in A, f ω ∂P) = _
  rw [← setIntegral_condExp hG hf hA]
  rw [setIntegral_congr_ae (hG _ hA) ((h u).mono (fun ω hω _ => hω))]
  rw [integral_const]
  have hg := charFun_gaussianReal (μ := (0:ℝ)) (v := v) u
  rw [charFun_apply_real] at hg
  rw [hg]
  simp [Measure.real,Measure.restrict_apply_univ,neg_div]

end Asakura.Chapter4

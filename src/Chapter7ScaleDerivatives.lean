import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Chapter7ClockODE
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.ContDiff.Deriv

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter7
set_option maxHeartbeats 2200000

noncomputable def scaleDensity (μ σ : ℝ → ℝ) (x0 x : ℝ) : ℝ :=
  Real.exp (-2*∫ z in x0..x,μ z/(σ z)^2)

noncomputable def scaleFunction (μ σ : ℝ → ℝ) (x0 x : ℝ) : ℝ :=
  ∫ y in x0..x,scaleDensity μ σ x0 y

theorem scale_derivatives
    (μ σ : ℝ → ℝ) (hμ : Continuous μ) (hσ : Continuous σ)
    (hσp : ∀ x,0 < σ x) (x0 : ℝ) :
    (∀ x,0 < scaleDensity μ σ x0 x) ∧
    (∀ x,HasDerivAt (scaleFunction μ σ x0) (scaleDensity μ σ x0 x) x) ∧
    (∀ x,HasDerivAt (scaleDensity μ σ x0)
      (-2*μ x/(σ x)^2*scaleDensity μ σ x0 x) x) ∧
    StrictMono (scaleFunction μ σ x0) ∧
    (∀ x,μ x*scaleDensity μ σ x0 x+
      (σ x)^2/2*(-2*μ x/(σ x)^2*scaleDensity μ σ x0 x) = 0) := by
  have hc : Continuous (fun z => μ z/(σ z)^2) := hμ.div (hσ.pow 2) (fun z => pow_ne_zero _ (ne_of_gt (hσp z)))
  have hd x : HasDerivAt (fun x => ∫ z in x0..x,μ z/(σ z)^2) (μ x/(σ x)^2) x :=
    intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
      hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  have hden x : HasDerivAt (scaleDensity μ σ x0)
      (-2*μ x/(σ x)^2*scaleDensity μ σ x0 x) x := by
    convert ((hd x).const_mul (-2)).exp using 1
    · funext y
      rfl
    · dsimp [scaleDensity]
      ring
  have hdc : Continuous (scaleDensity μ σ x0) := continuous_iff_continuousAt.mpr fun x => (hden x).continuousAt
  have hs x : HasDerivAt (scaleFunction μ σ x0) (scaleDensity μ σ x0 x) x :=
    intervalIntegral.integral_hasDerivAt_right (hdc.intervalIntegrable _ _)
      hdc.aestronglyMeasurable.stronglyMeasurableAtFilter hdc.continuousAt
  have hp x : 0 < scaleDensity μ σ x0 x := Real.exp_pos _
  refine ⟨hp,hs,hden,strictMono_of_hasDerivAt_pos hs hp,?_⟩
  intro x
  have hn := ne_of_gt (hσp x)
  field_simp
  <;> ring

end Asakura.Chapter7

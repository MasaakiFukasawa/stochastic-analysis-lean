import Chapter6ContinuousCoefficientMeasurable
import Chapter7DriftSquareGridBound
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter6

noncomputable def linearIntegratingFactor (α : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.exp (∫ r in 0..t,α r)

lemma integrating_factor_derivative (α : ℝ → ℝ) (hα : Continuous α) (t : ℝ) :
    HasDerivAt (linearIntegratingFactor α) (α t*linearIntegratingFactor α t) t := by
  have hi := intervalIntegral.integral_hasDerivAt_right (hα.intervalIntegrable 0 t)
    hα.aestronglyMeasurable.stronglyMeasurableAtFilter hα.continuousAt
  change HasDerivAt (fun x => Real.exp (∫ r in 0..x,α r)) (α t*Real.exp (∫ r in 0..t,α r)) t
  simpa only [mul_comm] using hi.exp

lemma integrating_factor_continuous (α : ℝ → ℝ) (hα : Continuous α) :
    Continuous (linearIntegratingFactor α) :=
  continuous_iff_continuousAt.mpr (fun t => (integrating_factor_derivative α hα t).continuousAt)

lemma integrating_factor_bounds (α : ℝ → ℝ) (K R : ℝ) (hK : 0≤K)
    (hb : ∀ r∈Icc 0 R,|α r|≤K) (t : ℝ) (ht : t∈Icc 0 R) :
    Real.exp (-K*R)≤linearIntegratingFactor α t ∧ linearIntegratingFactor α t≤Real.exp (K*R) := by
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := t) (f := α) (C := K)
    (fun r hr => by
      have hr0 : r∈Ioc 0 t := by simpa only [uIoc_of_le ht.1] using hr
      have hr' : r∈Icc 0 t := ⟨hr0.1.le,hr0.2⟩
      simpa only [Real.norm_eq_abs] using hb r ⟨hr'.1,hr'.2.trans ht.2⟩)
  simp only [Real.norm_eq_abs,sub_zero,abs_of_nonneg ht.1] at hi
  have hab : |∫ r in 0..t,α r|≤K*R := hi.trans (mul_le_mul_of_nonneg_left ht.2 hK)
  exact ⟨Real.exp_le_exp.mpr (by linarith [(abs_le.mp hab).1]),Real.exp_le_exp.mpr (abs_le.mp hab).2⟩

lemma integrating_factor_ratio (α : ℝ → ℝ) (hα : Continuous α) (s t : ℝ) :
    linearIntegratingFactor α t/linearIntegratingFactor α s=Real.exp (∫ r in s..t,α r) := by
  dsimp [linearIntegratingFactor]
  rw [← Real.exp_sub]
  congr 1
  have he := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hα.intervalIntegrable 0 s) (hα.intervalIntegrable s t)
  linarith

end Asakura.Chapter6

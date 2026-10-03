import Chapter5EnergyEstimates
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

open MeasureTheory
open scoped ENNReal
namespace Asakura.Chapter5

/-- Joint measurability and the printed Lipschitz hypothesis imply L2
membership after substitution of the input processes. The underlying
measurable space can be the progressive sigma algebra. -/
theorem generator_memLp {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω × (ℝ × ℝ) → ℝ) (hf : Measurable f)
    (Y Z : Ω → ℝ) (hY : Measurable Y) (hZ : Measurable Z)
    (iY : MemLp Y 2 μ) (iZ : MemLp Z 2 μ)
    (i0 : MemLp (fun ω => f (ω,0,0)) 2 μ)
    (C : ℝ) (hC : 0 ≤ C)
    (hl : ∀ ω y z, |f (ω,y,z)-f (ω,0,0)| ≤ C*(|y|+|z|)) :
    MemLp (fun ω => f (ω,Y ω,Z ω)) 2 μ := by
  have hi := i0.norm.add ((iY.norm.add iZ.norm).const_smul C)
  apply hi.mono' (hf.comp (measurable_id.prodMk (hY.prodMk hZ))).aestronglyMeasurable
  apply ae_of_all
  intro ω
  change |f (ω,Y ω,Z ω)| ≤ |f (ω,0,0)|+C*(|Y ω|+|Z ω|)
  have h := abs_add_le (f (ω,Y ω,Z ω)-f (ω,0,0)) (f (ω,0,0))
  simp only [sub_add_cancel] at h
  linarith [hl ω (Y ω) (Z ω)]

/-- Integrate the correct squared Lipschitz bound against the actual
weighted time-probability measure. -/
theorem generator_difference_energy {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (dY dZ dF : Ω → ℝ)
    (hY : MemLp dY 2 μ) (hZ : MemLp dZ 2 μ) (hF : MemLp dF 2 μ)
    (C : ℝ) (hC : 0 ≤ C)
    (hl : ∀ᵐ ω ∂μ, |dF ω| ≤ C*(|dY ω|+|dZ ω|)) :
    (∫ ω, (dF ω)^2 ∂μ) ≤
      2*C^2*((∫ ω, (dY ω)^2 ∂μ)+(∫ ω, (dZ ω)^2 ∂μ)) := by
  have iY : Integrable (fun ω => (dY ω)^2) μ := by
    simpa only [Real.norm_eq_abs,sq_abs] using hY.integrable_norm_pow (by norm_num : (2:ℕ) ≠ 0)
  have iZ : Integrable (fun ω => (dZ ω)^2) μ := by
    simpa only [Real.norm_eq_abs,sq_abs] using hZ.integrable_norm_pow (by norm_num : (2:ℕ) ≠ 0)
  have iF : Integrable (fun ω => (dF ω)^2) μ := by
    simpa only [Real.norm_eq_abs,sq_abs] using hF.integrable_norm_pow (by norm_num : (2:ℕ) ≠ 0)
  calc
    _ ≤ ∫ ω, 2*C^2*((dY ω)^2+(dZ ω)^2) ∂μ := by
      apply integral_mono_ae iF ((iY.add iZ).const_mul _)
      filter_upwards [hl] with ω hω
      exact Asakura.FullAudit.ch5_lipschitz_square _ _ _ C hC hω
    _ = _ := by rw [integral_const_mul,integral_add iY iZ]

end Asakura.Chapter5

import Chapter5Perturbation
import Chapter5WeightedSpace

open MeasureTheory Filter Asymptotics
open scoped Topology
namespace Asakura.Chapter5

/-- The constants in the perturbation proof can be chosen strictly
positive, uniformly in epsilon. This is stronger than merely lambda²>C. -/
theorem perturbation_positive_parameters (C β : ℝ) (hC : 0 ≤ C)
    (hβ : C*(2+C) < β) :
    ∃ μ ell : ℝ, 0 < μ ∧ 0 < ell ∧ C < ell^2 ∧ C*(2+ell^2)+μ^2 ≤ β := by
  let δ := (β-C*(2+C))/(2*(C+1))
  have hδ : 0 < δ := div_pos (sub_pos.mpr hβ) (by positivity)
  have he : δ*(2*(C+1)) = β-C*(2+C) := div_mul_cancel₀ _ (by positivity)
  have hp : 0 < C+δ := add_pos_of_nonneg_of_pos hC hδ
  refine ⟨Real.sqrt δ,Real.sqrt (C+δ),Real.sqrt_pos.mpr hδ,Real.sqrt_pos.mpr hp,?_,?_⟩
  · rw [Real.sq_sqrt hp.le]; linarith
  · rw [Real.sq_sqrt hp.le,Real.sq_sqrt hδ.le]
    nlinarith [mul_nonneg hC hδ.le]

/-- The weighted estimates imply every lower-weight estimate on a finite
time interval. This justifies changing beta in the perturbation theorem. -/
theorem weighted_energy_comparison {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure (Ω × ℝ)) (H : Ω × ℝ → ℝ) (β γ T : ℝ)
    (hT : 0 ≤ T) (hs : ∀ᵐ z ∂ν, z.2 ∈ Set.Icc 0 T)
    (hβ : Integrable (fun z => Real.exp (β*z.2)*H z^2) ν)
    (hγ : Integrable (fun z => Real.exp (γ*z.2)*H z^2) ν) :
    (∫ z, Real.exp (β*z.2)*H z^2 ∂ν) ≤
      Real.exp (|β-γ| * T) * ∫ z, Real.exp (γ*z.2)*H z^2 ∂ν := by
  rw [← integral_const_mul]
  apply integral_mono_ae hβ (hγ.const_mul _)
  filter_upwards [hs] with z hz
  have hex : β*z.2 ≤ |β-γ| * T+γ*z.2 := by
    have h1 := mul_le_mul_of_nonneg_right (le_abs_self (β-γ)) hz.1
    have h2 := mul_le_mul_of_nonneg_left hz.2 (abs_nonneg (β-γ))
    nlinarith
  have hh := Real.exp_le_exp.mpr hex
  rw [Real.exp_add] at hh
  nlinarith [mul_nonneg (sq_nonneg (H z)) (sub_nonneg.mpr hh)]

end Asakura.Chapter5

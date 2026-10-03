import Chapter6AffineDensity
import Chapter6GaussianDensityFormula
import Chapter6ProductDensity
import Chapter12WienerCoordinates
import Mathlib.Analysis.Calculus.ContDiff.Operations

open MeasureTheory ProbabilityTheory
namespace Asakura.Chapter12
open Asakura.Chapter6
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000

noncomputable def affineGaussianDensity {d : ℕ}
    (L : (Fin d → ℝ) ≃L[ℝ] (Fin d → ℝ)) (b : Fin d → ℝ) (x : Fin d → ℝ) : ℝ :=
  |(LinearMap.det L.toLinearMap)⁻¹| *(Real.sqrt (2*Real.pi))⁻¹^d*
    Real.exp (-(∑ i,(L.symm (x-b) i)^2)/2)

theorem affine_gaussian_density_smooth {d : ℕ}
    (L : (Fin d → ℝ) ≃L[ℝ] (Fin d → ℝ)) (b : Fin d → ℝ) :
    ContDiff ℝ ⊤ (affineGaussianDensity L b) := by
  unfold affineGaussianDensity
  fun_prop

theorem affine_gaussian_density_positive {d : ℕ}
    (L : (Fin d → ℝ) ≃L[ℝ] (Fin d → ℝ)) (b x : Fin d → ℝ) :
    0<affineGaussianDensity L b x := by
  unfold affineGaussianDensity
  have hd := L.toLinearEquiv.isUnit_det'.ne_zero
  exact mul_pos (mul_pos (abs_pos.mpr (inv_ne_zero hd))
    (pow_pos (inv_pos.mpr (Real.sqrt_pos.mpr (by positivity))) _)) (Real.exp_pos _)

theorem affine_gaussian_density_law {d : ℕ}
    (L : (Fin d → ℝ) ≃L[ℝ] (Fin d → ℝ)) (b : Fin d → ℝ) :
    (Measure.pi (fun _ : Fin d => gaussianReal 0 1)).map (fun z => b+L z)=
      volume.withDensity (fun x => ENNReal.ofReal (affineGaussianDensity L b x)) := by
  rw [independent_gaussian_density (1:NNReal) one_ne_zero]
  have hh := affine_map_real_density L b (fun z => ∏ i,gaussianPDFReal 0 1 (z i)) (by fun_prop)
  change ((volume : Measure (Fin d → ℝ)).withDensity _).map (fun z => b+L z)=_ at hh
  rw [hh]
  congr 1
  funext x
  congr 1
  rw [gaussian_product_formula]
  simp only [NNReal.coe_one,mul_one]
  unfold affineGaussianDensity
  ring

/-- An invertible linear transform of actual orthonormal Wiener coordinates
has an everywhere positive smooth density. -/
theorem wiener_affine_smooth_density {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (P : Measure Ω) [IsProbabilityMeasure P] (W : H →ₗᵢ[ℝ] Lp ℝ 2 P)
    (hlaw : ∀ h,HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    {d : ℕ} (e : Fin d → H) (he : Orthonormal ℝ e)
    (L : (Fin d → ℝ) ≃L[ℝ] (Fin d → ℝ)) (b : Fin d → ℝ) :
    HasLaw (fun w => b+L (fun i => W (e i) w))
      (volume.withDensity (fun x => ENNReal.ofReal (affineGaussianDensity L b x))) P ∧
    ContDiff ℝ ⊤ (affineGaussianDensity L b) ∧
    (∀ x,0<affineGaussianDensity L b x) := by
  refine ⟨?_,affine_gaussian_density_smooth L b,affine_gaussian_density_positive L b⟩
  have hh := (hasLaw_map (P := Measure.pi (fun _ : Fin d => gaussianReal 0 1))
    (show AEMeasurable (fun z => b+L z) _ from (show Measurable (fun z => b+L z) by fun_prop).aemeasurable)).comp
    (wiener_orthonormal_law P W hlaw e he)
  rw [affine_gaussian_density_law] at hh
  exact hh

end Asakura.Chapter12

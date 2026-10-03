import Chapter6AffineDensity
import Chapter6GaussianDensityFormula
import Chapter6ProductDensity

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
namespace Asakura.Chapter8
open Asakura.Chapter6
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- A normalized positive quadratic density is the law of an invertible
linear transform of independent standard normal coordinates. -/
theorem affine_quadratic_density {d : ℕ}
    (L : (Fin d → ℝ) ≃L[ℝ] (Fin d → ℝ))
    (U : (Fin d → ℝ) → ℝ) (hU : Continuous U) (β : ℝ)
    (hform : ∀ x,(∑ i,(L.symm x i)^2)/2=β*U x) :
    volume.withDensity (fun x : Fin d → ℝ => ENNReal.ofReal
      ((∫ y : Fin d → ℝ,Real.exp (-β*U y))⁻¹*Real.exp (-β*U x)))=
      (Measure.pi (fun _ : Fin d => gaussianReal 0 1)).map L := by
  let c := |(LinearMap.det L.toLinearMap)⁻¹| *(Real.sqrt (2*Real.pi))⁻¹^d
  let ρ := fun x : Fin d → ℝ => Real.exp (-β*U x)
  have hc : 0<c := by
    dsimp [c]
    have hd := L.toLinearEquiv.isUnit_det'.ne_zero
    exact mul_pos (abs_pos.mpr (inv_ne_zero hd)) (pow_pos (inv_pos.mpr (Real.sqrt_pos.mpr (by positivity))) _)
  have hρ x : 0<ρ x := Real.exp_pos _
  have hρm : Measurable ρ := Real.continuous_exp.measurable.comp ((hU.const_mul (-β)).measurable)
  have he x : |(LinearMap.det L.toLinearMap)⁻¹| *(∏ i,gaussianPDFReal 0 1 (L.symm (x-0) i))=c*ρ x := by
    rw [sub_zero,gaussian_product_formula]
    simp only [NNReal.coe_one,mul_one]
    have hf : -(∑ i,(L.symm x i)^2)/2= -β*U x := by linarith [hform x]
    rw [hf]
    dsimp [c,ρ]
    ring
  have hmap : (Measure.pi (fun _ : Fin d => gaussianReal 0 1)).map L=
      volume.withDensity (fun x => ENNReal.ofReal (c*ρ x)) := by
    rw [independent_gaussian_density (1:ℝ≥0) one_ne_zero]
    have hh := affine_map_real_density L 0 (fun y => ∏ i,gaussianPDFReal 0 1 (y i)) (by fun_prop)
    have hL : (affineMeasurableEquiv L 0 : (Fin d → ℝ) → (Fin d → ℝ))=L := by
      funext x
      change 0+L x=L x
      exact zero_add _
    rw [hL] at hh
    simpa only [he] using hh
  haveI : IsProbabilityMeasure ((Measure.pi (fun _ : Fin d => gaussianReal 0 1)).map L) :=
    (Measure.isProbabilityMeasure_map_iff L.continuous.measurable.aemeasurable).mpr inferInstance
  have hi : (∫ x : Fin d → ℝ,(1:ℝ) ∂(Measure.pi (fun _ : Fin d => gaussianReal 0 1)).map L)=1 := by simp
  rw [hmap,integral_withDensity_eq_integral_toReal_smul
    (hρm.const_mul c).ennreal_ofReal (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))] at hi
  have hfun : (fun x => (ENNReal.ofReal (c*ρ x)).toReal • (1:ℝ))=fun x => c*ρ x := by
    funext x
    rw [ENNReal.toReal_ofReal (mul_nonneg hc.le (hρ x).le),smul_eq_mul,mul_one]
  rw [hfun,integral_const_mul] at hi
  have hZ : (∫ x,ρ x)≠0 := by intro hz; rw [hz,mul_zero] at hi; norm_num at hi
  have hnorm : (∫ x,ρ x)⁻¹=c := by
    calc
      _ = (c*(∫ x,ρ x))*(∫ x,ρ x)⁻¹ := by rw [hi,one_mul]
      _ = c := by rw [mul_assoc,mul_inv_cancel₀ hZ,mul_one]
  rw [hmap]
  change volume.withDensity (fun x => ENNReal.ofReal ((∫ y,ρ y)⁻¹*ρ x))=_
  rw [hnorm]
end Asakura.Chapter8

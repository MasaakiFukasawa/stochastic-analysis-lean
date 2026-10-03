import Chapter8MaxwellDensity
import Chapter8ThreeDimensionalRadialIntegral

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ENNReal
namespace Asakura.Chapter8
set_option maxHeartbeats 1400000

/-- Integrating a function of Euclidean speed under the three-dimensional
Maxwell law gives the radial density, including its Jacobian. -/
theorem gaussian_speed_integral (t : ℝ≥0) (ht : t≠0) (f : ℝ → ℝ) :
    (∫ v : Fin 3 → ℝ,f ‖WithLp.toLp 2 v‖ ∂Measure.pi (fun _ => gaussianReal 0 t))=
      ∫ r in Ioi (0:ℝ),
        4*Real.pi*r^2*(Real.sqrt (2*Real.pi*(t:ℝ)))⁻¹^3*
          Real.exp (-r^2/(2*(t:ℝ)))*f r := by
  rw [Asakura.Chapter6.independent_gaussian_density t ht]
  have hm : Measurable (fun v : Fin 3 → ℝ => ENNReal.ofReal (∏ i,gaussianPDFReal 0 t (v i))) := by fun_prop
  have hfin : ∀ᵐ v ∂(volume : Measure (Fin 3 → ℝ)),
      ENNReal.ofReal (∏ i,gaussianPDFReal 0 t (v i))<⊤ := ae_of_all _ (fun _ => ENNReal.ofReal_lt_top)
  rw [integral_withDensity_eq_integral_toReal_smul hm hfin]
  have hpdf (v : Fin 3 → ℝ) : 0≤∏ i : Fin 3,gaussianPDFReal 0 t (v i) :=
    Finset.prod_nonneg (fun i _ => gaussianPDFReal_nonneg _ _ _)
  simp_rw [ENNReal.toReal_ofReal (hpdf _),smul_eq_mul,Asakura.Chapter6.gaussian_product_formula]
  let c := (Real.sqrt (2*Real.pi*(t:ℝ)))⁻¹^3
  have he := (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 3)).integral_comp'
    (fun v : Fin 3 → ℝ => c*Real.exp (-(∑ i,v i^2)/(2*(t:ℝ)))*f ‖WithLp.toLp 2 v‖)
  have heq : (∫ v : Fin 3 → ℝ,c*Real.exp (-(∑ i,v i^2)/(2*(t:ℝ)))*f ‖WithLp.toLp 2 v‖)=
      ∫ v : EuclideanSpace ℝ (Fin 3),c*Real.exp (-‖v‖^2/(2*(t:ℝ)))*f ‖v‖ := by
    rw [←he]
    apply integral_congr_ae
    apply ae_of_all
    intro v
    simp only [MeasurableEquiv.coe_toLp_symm,WithLp.toLp_ofLp,EuclideanSpace.real_norm_sq_eq]
  change (∫ v : Fin 3 → ℝ,c*Real.exp (-(∑ i,v i^2)/(2*(t:ℝ)))*f ‖WithLp.toLp 2 v‖)=_
  rw [heq,three_dimensional_radial_integral (fun r => c*Real.exp (-r^2/(2*(t:ℝ)))*f r)]
  rw [←integral_const_mul]
  apply integral_congr_ae
  apply ae_of_all
  intro r
  dsimp only [c]
  ring

/-- The exact speed density printed in the manuscript, with physical
parameters beta and m; the formula holds against every real test function. -/
theorem maxwell_speed_density (β m : ℝ) (hβ : 0<β) (hm : 0<m) (f : ℝ → ℝ) :
    (∫ v : Fin 3 → ℝ,f ‖WithLp.toLp 2 v‖ ∂Measure.pi
      (fun _ => gaussianReal 0 ⟨(β*m)⁻¹,by positivity⟩))=
      ∫ r in Ioi (0:ℝ),
        4*Real.pi*r^2*(β*m/(2*Real.pi))^((3:ℝ)/2)*Real.exp (-β*m*r^2/2)*f r := by
  let t : ℝ≥0 := ⟨(β*m)⁻¹,by positivity⟩
  have ht : t≠0 := by
    intro h
    have hz := congrArg (fun a : ℝ≥0 => (a:ℝ)) h
    change (β*m)⁻¹=0 at hz
    exact (inv_ne_zero (mul_ne_zero hβ.ne' hm.ne')) hz
  rw [gaussian_speed_integral t ht]
  have hs : (Real.sqrt (2*Real.pi*(t:ℝ)))⁻¹=Real.sqrt (β*m/(2*Real.pi)) := by
    rw [←Real.sqrt_inv]
    congr 1
    change (2*Real.pi*(β*m)⁻¹)⁻¹=β*m/(2*Real.pi)
    field_simp
  have hc : (Real.sqrt (2*Real.pi*(t:ℝ)))⁻¹^3=(β*m/(2*Real.pi))^((3:ℝ)/2) := by
    rw [hs,Asakura.Chapter6.gaussian_sqrt_power _ (by positivity)]
    norm_num
  apply integral_congr_ae
  apply ae_of_all
  intro r
  rw [hc]
  have he : -r^2/(2*(t:ℝ))= -β*m*r^2/2 := by
    change -r^2/(2*((β*m)⁻¹))= -β*m*r^2/2
    field_simp
    <;> ring
  dsimp only
  rw [he]

end Asakura.Chapter8

import Chapter6GaussianDensityFormula
import Chapter6ProductDensity
import Chapter8HamiltonianIntegrability

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal
namespace Asakura.Chapter8
set_option maxHeartbeats 1800000

/-- Identify the normalized velocity Gibbs density with the independent
centered Gaussian coordinates of variance (beta*m)^(-1). -/
theorem maxwell_density (d : ℕ) (β m : ℝ) (hβ : 0<β) (hm : 0<m) :
    (volume.withDensity (fun v : Fin d → ℝ => ENNReal.ofReal
      ((∫ y : Fin d → ℝ,Real.exp (-(β*m/2)*∑ i,y i^2))⁻¹*Real.exp (-(β*m/2)*∑ i,v i^2))))=
    Measure.pi (fun _ : Fin d => gaussianReal 0 ⟨(β*m)⁻¹,by positivity⟩) := by
  let t : ℝ≥0 := ⟨(β*m)⁻¹,by positivity⟩
  have ht : t≠0 := by
    intro h
    have hh := congrArg (fun r : ℝ≥0 => (r:ℝ)) h
    change (β*m)⁻¹=0 at hh
    exact (inv_ne_zero (mul_ne_zero hβ.ne' hm.ne')) hh
  let c := (Real.sqrt (2*Real.pi*(t:ℝ)))⁻¹^d
  let Z := ∫ y : Fin d → ℝ,Real.exp (-(β*m/2)*∑ i,y i^2)
  have he (v : Fin d → ℝ) : (∏ i,gaussianPDFReal 0 t (v i))=c*Real.exp (-(β*m/2)*∑ i,v i^2) := by
    rw [Asakura.Chapter6.gaussian_product_formula]
    congr 2
    change -(∑ i,v i^2)/(2*((β*m)⁻¹))= -(β*m/2)*∑ i,v i^2
    field_simp
    <;> ring
  have hi : (∫ v : Fin d → ℝ,∏ i,gaussianPDFReal 0 t (v i))=1 := by
    rw [integral_fintype_prod_volume_eq_prod]
    simp [integral_gaussianPDFReal_eq_one 0 ht]
  simp_rw [he] at hi
  rw [integral_const_mul] at hi
  change c*Z=1 at hi
  have hZ : Z≠0 := by intro hz; rw [hz,mul_zero] at hi; norm_num at hi
  have hinv : Z⁻¹=c := by
    calc
      _ = (c*Z)*Z⁻¹ := by rw [hi,one_mul]
      _ = c := by rw [mul_assoc,mul_inv_cancel₀ hZ,mul_one]
  rw [Asakura.Chapter6.independent_gaussian_density t ht]
  apply congrArg (fun h : (Fin d → ℝ) → ℝ≥0∞ => volume.withDensity h)
  funext v
  rw [he]
  change ENNReal.ofReal (Z⁻¹*Real.exp (-(β*m/2)*∑ i,v i^2))=_
  rw [hinv]

end Asakura.Chapter8

import Chapter9GaussianKernel
import Chapter6ProductDensity

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators ENNReal NNReal
namespace Asakura.Chapter9
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

theorem gaussian_kernel_product {d : ℕ} (a : ℝ) (v : ℝ≥0) (hv : v≠0)
    (x y : Fin d → ℝ) :
    gaussianKernel a v x y=∏ i,gaussianPDFReal (a*x i) v (y i) := by
  have hpos : 0<2*Real.pi*(v:ℝ) := by positivity
  have he i : gaussianPDFReal (a*x i) v (y i)=
      Real.exp (-(1/2:ℝ)*Real.log (2*Real.pi*(v:ℝ))-(y i-a*x i)^2/(2*(v:ℝ))) := by
    rw [Real.exp_sub]
    have hs : Real.exp (-(1/2:ℝ)*Real.log (2*Real.pi*(v:ℝ)))=
        (Real.sqrt (2*Real.pi*(v:ℝ)))⁻¹ := by
      rw [show -(1/2:ℝ)*Real.log (2*Real.pi*(v:ℝ))= -Real.log (Real.sqrt (2*Real.pi*(v:ℝ))) by
        rw [Real.log_sqrt hpos.le]; ring,Real.exp_neg,Real.exp_log (Real.sqrt_pos.mpr hpos)]
    rw [hs]
    simp only [gaussianPDFReal,←Real.exp_neg,neg_div,div_eq_mul_inv,neg_mul]
  rw [show (∏ i,gaussianPDFReal (a*x i) v (y i))=
      ∏ i,Real.exp (-(1/2:ℝ)*Real.log (2*Real.pi*(v:ℝ))-(y i-a*x i)^2/(2*(v:ℝ))) by simp_rw [he],←Real.exp_sum]
  unfold gaussianKernel
  congr 1
  simp only [sum_sub_distrib,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,←sum_div]
  ring

theorem gaussian_kernel_density {d : ℕ} (a : ℝ) (v : ℝ≥0) (hv : v≠0)
    (x : Fin d → ℝ) :
    Measure.pi (fun i => gaussianReal (a*x i) v)=
      (volume : Measure (Fin d → ℝ)).withDensity (fun y => ENNReal.ofReal (gaussianKernel a v x y)) := by
  simp_rw [gaussian_kernel_product a v hv]
  apply Asakura.Chapter6.finite_product_real_density _ _
    (fun _ => measurable_gaussianPDFReal _ _) (fun _ => integrable_gaussianPDFReal _ _)
    (fun _ => gaussianPDFReal_nonneg _ _)
  intro i
  exact gaussianReal_of_var_ne_zero _ hv

theorem gaussian_kernel_integral {d : ℕ} (a : ℝ) (v : ℝ≥0) (hv : v≠0)
    (x : Fin d → ℝ) :
    Integrable (gaussianKernel a v x) ∧ (∫ y,gaussianKernel a v x y)=1 := by
  change Integrable (fun y => gaussianKernel a v x y) ∧ _
  simp_rw [gaussian_kernel_product a v hv]
  rw [volume_pi]
  refine ⟨Integrable.fintype_prod (fun i => integrable_gaussianPDFReal (a*x i) v),?_⟩
  rw [integral_fintype_prod_eq_prod]
  simp [integral_gaussianPDFReal_eq_one _ hv]
end Asakura.Chapter9

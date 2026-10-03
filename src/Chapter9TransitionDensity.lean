import Chapter9GaussianObservation
import Chapter9OULaw

open MeasureTheory ProbabilityTheory Matrix
open scoped NNReal ENNReal
namespace Asakura.Chapter9
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

theorem isotropic_gaussian_affine_density {d : ℕ} (a : ℝ) (v : ℝ≥0) (hv : v≠0)
    (x : Fin d → ℝ) :
    (multivariateGaussian 0 ((v:ℝ) • (1 : Matrix (Fin d) (Fin d) ℝ))).map
      (fun ξ : EuclideanSpace ℝ (Fin d) => fun i => a*x i+ξ i)=
      (volume : Measure (Fin d → ℝ)).withDensity (fun y => ENNReal.ofReal (gaussianKernel a v x y)) := by
  have hs := standard_gaussian_scaled d (Real.sqrt (v:ℝ))
  rw [Real.sq_sqrt v.coe_nonneg] at hs
  rw [←hs,Measure.map_map (by fun_prop) (by fun_prop),←map_pi_eq_stdGaussian,
    Measure.map_map (by fun_prop) (by fun_prop)]
  have he : (fun ξ : Fin d → ℝ =>
      (fun ξ : EuclideanSpace ℝ (Fin d) => fun i => a*x i+ξ i)
        (Real.sqrt (v:ℝ) • WithLp.toLp 2 ξ))=
      (fun ξ i => a*x i+Real.sqrt (v:ℝ)*ξ i) := rfl
  change (Measure.pi (fun _ : Fin d => gaussianReal 0 1)).map
    (fun ξ i => a*x i+Real.sqrt (v:ℝ)*ξ i)=_
  rw [gaussian_affine_coordinate_law,gaussian_kernel_density a v hv]
end Asakura.Chapter9

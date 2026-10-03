import Chapter9MixtureScore
import Chapter9GaussianKernel
import Mathlib.Analysis.InnerProductSpace.PiL2

open MeasureTheory
open scoped RealInnerProductSpace
namespace Asakura.Chapter9
set_option maxHeartbeats 1400000

/-- Identify the Hilbert-space kernel with the coordinate density in the
manuscript, retaining the Euclidean rather than the sup norm. -/
theorem gaussian_kernel_radial {d : ℕ} (a v : ℝ)
    (x y : EuclideanSpace ℝ (Fin d)) :
    gaussianKernel a v (fun i => x i) (fun i => y i)=
      radialKernel (Real.exp (-(d:ℝ)/2*Real.log (2*Real.pi*v))) a v x y := by
  unfold gaussianKernel radialKernel
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [PiLp.sub_apply,PiLp.smul_apply,smul_eq_mul]
  rw [←Real.exp_add]
  congr 1
  ring

/-- The logarithmic derivative of the manuscript's coordinate density,
after integration against the actual initial probability measure. -/
theorem euclidean_mixture_score {d : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (a v : ℝ) (hv : 0<v) (y : EuclideanSpace ℝ (Fin d)) :
    let p := fun z : EuclideanSpace ℝ (Fin d) =>
      ∫ x,gaussianKernel a v (fun i => x i) (fun i => z i) ∂μ
    let P := μ.withDensity (fun x => ENNReal.ofReal
      (gaussianKernel a v (fun i => x i) (fun i => y i)/p y))
    IsProbabilityMeasure P ∧
      HasFDerivAt (fun z => Real.log (p z))
        (innerSL ℝ (∫ x,(-1/v) • (y-a • x) ∂P)) y := by
  dsimp only
  simp_rw [gaussian_kernel_radial]
  exact radial_mixture_score μ _ a v (Real.exp_pos _) hv y
end Asakura.Chapter9

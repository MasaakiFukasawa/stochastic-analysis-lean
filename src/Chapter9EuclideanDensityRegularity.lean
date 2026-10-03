import Chapter9GaussianSmoothness
import Chapter9EuclideanScore

open MeasureTheory Set
open scoped ContDiff
namespace Asakura.Chapter9
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

noncomputable def ouEuclideanDensity {d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d)))
    (z : ℝ × EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∫ x,gaussianKernel (Real.exp (-z.1)) (1-Real.exp (-2*z.1))
    (fun i => x i) (fun i => z.2 i) ∂μ

 theorem euclidean_density_coordinate_map {d : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin d))) (z : ℝ × EuclideanSpace ℝ (Fin d)) :
    ouEuclideanDensity μ z=
      ∫ x,Real.exp (ouExponent x (z.1,fun i => z.2 i)) ∂(μ.map WithLp.ofLp) := by
  rw [integral_map ((WithLp.measurable_ofLp 2 _).aemeasurable) (by apply Continuous.aestronglyMeasurable; dsimp [ouExponent]; fun_prop)]
  rfl

/-- The previously verified coordinate mixture regularity applies to the
same density on Euclidean space, with its Euclidean norm and gradient. -/
theorem ou_euclidean_density_smooth {d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d)))
    [IsFiniteMeasure μ] : ContDiffOn ℝ ∞ (ouEuclideanDensity μ) {z | 0<z.1} := by
  let C := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)
  let L : (ℝ × EuclideanSpace ℝ (Fin d)) →L[ℝ] (ℝ × (Fin d → ℝ)) :=
    (ContinuousLinearMap.id ℝ ℝ).prodMap C.toContinuousLinearMap
  have h := (ou_gaussian_mixture_smooth (μ.map WithLp.ofLp)).comp L.contDiff.contDiffOn
    (show Set.MapsTo L {z | 0<z.1} {z | 0<z.1} from fun z hz => hz)
  have he : ouEuclideanDensity μ=(fun z =>
      ∫ x,Real.exp (ouExponent x (L z)) ∂(μ.map WithLp.ofLp)) := by
    funext z
    exact euclidean_density_coordinate_map μ z
  rw [he]
  exact h

 theorem euclidean_density_radial {d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d)))
    (t : ℝ) (y : EuclideanSpace ℝ (Fin d)) :
    ouEuclideanDensity μ (t,y)=
      ∫ x,radialKernel (Real.exp (-(d:ℝ)/2*Real.log (2*Real.pi*(1-Real.exp (-2*t)))))
        (Real.exp (-t)) (1-Real.exp (-2*t)) x y ∂μ := by
  unfold ouEuclideanDensity
  simp_rw [gaussian_kernel_radial]
end Asakura.Chapter9

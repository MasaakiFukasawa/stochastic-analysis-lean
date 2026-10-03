import Chapter9ScoreDerivative
import Chapter9EuclideanScore
import Chapter9ScoreIntegrability

open MeasureTheory
open scoped RealInnerProductSpace
namespace Asakura.Chapter9
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

noncomputable def mixtureScore {d : ℕ} (μ : Measure (Fin d → ℝ)) (a v : ℝ)
    (y : Fin d → ℝ) : EuclideanSpace ℝ (Fin d) :=
  (∫ x,gaussianKernel a v x y ∂μ)⁻¹ •
    (∫ x,gaussianKernel a v x y • componentScore a v (x,y) ∂μ)

/-- Coordinate prior measures and Euclidean gradients describe the same
mixture. The score used in the conditional-expectation theorem is the
actual logarithmic gradient of that mixture density. -/
theorem coordinate_mixture_log_gradient {d : ℕ}
    (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (a v : ℝ) (hv : 0<v) (y : EuclideanSpace ℝ (Fin d)) :
    HasFDerivAt (fun z : EuclideanSpace ℝ (Fin d) =>
      Real.log (∫ x,gaussianKernel a v x (fun i => z i) ∂μ))
      (innerSL ℝ (mixtureScore μ a v (fun i => y i))) y := by
  let c := Real.exp (-(d:ℝ)/2*Real.log (2*Real.pi*v))
  let μE := μ.map (WithLp.toLp 2)
  have hto : Measurable (WithLp.toLp 2 : (Fin d → ℝ) → EuclideanSpace ℝ (Fin d)) :=
    WithLp.measurable_toLp 2 _
  haveI : IsProbabilityMeasure μE := (Measure.isProbabilityMeasure_map_iff hto.aemeasurable).mpr inferInstance
  have hk (x : Fin d → ℝ) (z : EuclideanSpace ℝ (Fin d)) :
      radialKernel c a v (WithLp.toLp 2 x) z=gaussianKernel a v x (fun i => z i) := by
    exact (gaussian_kernel_radial a v (WithLp.toLp 2 x) z).symm
  have hp (z : EuclideanSpace ℝ (Fin d)) :
      (∫ x,radialKernel c a v x z ∂μE)=∫ x,gaussianKernel a v x (fun i => z i) ∂μ := by
    rw [integral_map hto.aemeasurable (by unfold radialKernel; fun_prop)]
    apply integral_congr_ae
    exact ae_of_all _ (fun x => hk x z)
  have hg (z : EuclideanSpace ℝ (Fin d)) :
      (∫ x,(-radialKernel c a v x z/v) • (z-a • x) ∂μE)=
        ∫ x,gaussianKernel a v x (fun i => z i) • componentScore a v (x,fun i => z i) ∂μ := by
    rw [integral_map hto.aemeasurable (by unfold radialKernel; fun_prop)]
    apply integral_congr_ae
    apply ae_of_all
    intro x
    dsimp only
    rw [hk]
    ext i
    simp only [componentScore,PiLp.smul_apply,PiLp.sub_apply,WithLp.ofLp_toLp,smul_eq_mul]
    ring
  have hd := radial_log_density_fderiv μE c a v (Real.exp_pos _) hv y
  dsimp only at hd
  simpa only [hp,hg,mixtureScore] using hd
end Asakura.Chapter9

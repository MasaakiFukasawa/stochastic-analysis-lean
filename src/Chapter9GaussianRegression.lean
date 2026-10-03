import Chapter9KernelRegression
import Chapter9PosteriorMeasure

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace Asakura.Chapter9
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

/-- Conditional expectation under the joint Gaussian transition law,
for an arbitrary initial probability distribution, including atomic ones. -/
theorem gaussian_joint_regression {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (a : ℝ) (v : ℝ≥0) (hv : v≠0)
    (f : (Fin d → ℝ) × (Fin d → ℝ) → E) (hmf : StronglyMeasurable f)
    (hf : Integrable f ((μ.prod volume).withDensity
      (fun z => ENNReal.ofReal (gaussianKernel a v z.1 z.2)))) :
    let Q := (μ.prod volume).withDensity (fun z => ENNReal.ofReal (gaussianKernel a v z.1 z.2))
    Q[f|MeasurableSpace.comap Prod.snd inferInstance] =ᵐ[Q]
      (fun z => ∫ x,f (x,z.2) ∂μ.withDensity (fun x => ENNReal.ofReal
        (gaussianKernel a v x z.2/(∫ u,gaussianKernel a v u z.2 ∂μ)))) := by
  let φ := fun y : Fin d → ℝ => gaussianKernel 0 1 (fun _ => 0) y
  let ρ := Measure.pi (fun _ : Fin d => gaussianReal 0 1)
  have hφ : Measurable φ := by unfold φ gaussianKernel; fun_prop
  have hφpos y : 0<φ y := gaussian_kernel_positive _ _ _ _
  have hρ : ρ=volume.withDensity (fun y => ENNReal.ofReal (φ y)) := by
    simpa [ρ,φ] using gaussian_kernel_density (d := d) 0 1 (by norm_num) (fun _ => 0)
  have hk : Measurable (fun z : (Fin d → ℝ) × (Fin d → ℝ) => gaussianKernel a v z.1 z.2) := by
    unfold gaussianKernel
    fun_prop
  have hb := kernel_regression μ volume ρ φ hφ hφpos hρ
    (fun z => gaussianKernel a v z.1 z.2) hk
    (fun z => gaussian_kernel_positive a v z.1 z.2)
    (fun x => (gaussian_kernel_integral a v hv x).1)
    (fun x => (gaussian_kernel_integral a v hv x).2) f hmf hf
  apply hb.trans
  apply ae_of_all
  intro z
  symm
  apply normalized_density_integral μ (fun x => gaussianKernel a v x z.2)
    (by unfold gaussianKernel; fun_prop)
    (fun x => (gaussian_kernel_positive a v x z.2).le)
    _ (gaussian_mixture_positive μ a v hv z.2).2
end Asakura.Chapter9

import Chapter12GaussianLinearScoreLaw
import Chapter12GaussianTiltDerivative

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

/-- Gaussian smoothing differentiates a merely measurable L2 payoff.
The proof differentiates the density, with domination proved above. -/
theorem finite_gaussian_translation_derivative {d : ℕ} (q : Fin d → ℝ)
    (f : (Fin d → ℝ) → ℝ) (hm : Measurable f)
    (hf : MemLp f 2 (Measure.pi (fun _ : Fin d => gaussianReal 0 1))) (t : ℝ) :
    HasDerivAt (fun s : ℝ => ∫ z,f (s • q+z) ∂Measure.pi (fun _ : Fin d => gaussianReal 0 1))
      (∫ z,f z*Real.exp (t*(∑ i,q i*z i)-t^2*(∑ i,(q i)^2)/2)*
        ((∑ i,q i*z i)-t*(∑ i,(q i)^2))
        ∂Measure.pi (fun _ : Fin d => gaussianReal 0 1)) t := by
  have hh := gaussian_tilt_expectation_derivative
    (Measure.pi (fun _ : Fin d => gaussianReal 0 1)) (fun z => ∑ i,q i*z i) f
    ⟨∑ i,(q i)^2,Finset.sum_nonneg (fun i _ => sq_nonneg _)⟩
    (finite_gaussian_linear_score_law q) hf t
  have he : (fun s : ℝ => ∫ z,f (s • q+z) ∂Measure.pi (fun _ : Fin d => gaussianReal 0 1))=
      (fun s : ℝ => ∫ z,f z*Real.exp (s*(∑ i,q i*z i)-s^2*(∑ i,(q i)^2)/2)
        ∂Measure.pi (fun _ : Fin d => gaussianReal 0 1)) :=
    funext (fun s => standard_gaussian_translation_integral q s f hm)
  rw [he]
  exact hh

theorem finite_gaussian_translation_derivative_zero {d : ℕ} (q : Fin d → ℝ)
    (f : (Fin d → ℝ) → ℝ) (hm : Measurable f)
    (hf : MemLp f 2 (Measure.pi (fun _ : Fin d => gaussianReal 0 1))) :
    HasDerivAt (fun s : ℝ => ∫ z,f (s • q+z) ∂Measure.pi (fun _ : Fin d => gaussianReal 0 1))
      (∫ z,f z*(∑ i,q i*z i) ∂Measure.pi (fun _ : Fin d => gaussianReal 0 1)) 0 := by
  simpa only [zero_mul,zero_pow (by omega : 2≠0),zero_div,sub_zero,Real.exp_zero,mul_one]
    using finite_gaussian_translation_derivative q f hm hf 0

end Asakura.Chapter12

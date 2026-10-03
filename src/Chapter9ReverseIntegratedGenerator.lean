import Chapter9ReverseKernelDerivative
import Chapter9ReverseGeneratorIntegralBound
import Chapter9BoundedDerivativeFTC

open MeasureTheory Set Filter
open scoped Topology ContDiff
namespace Asakura.Chapter9
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

/-- The complete analytic reverse-kernel identity, including the singular
lower endpoint. Differentiation, integration by parts, endpoint convergence,
and integrability are all derived for the actual OU density and kernel. -/
theorem reverse_ou_integrated_generator {d : ℕ}
    (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (f : (Fin d → ℝ) → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (τ b : ℝ) (hb : 0<b) (hbτ : b<τ) (x : Fin d → ℝ) :
    let p := fun t y => ∫ z,Real.exp (ouExponent z (t,y)) ∂μ
    let k := fun h y => gaussianKernel (Real.exp (-h)) (1-Real.exp (-2*h)) y x
    let G := fun h => (∫ y,p (τ-h) y*reverseTest (p (τ-h)) f y*k h y)/p τ x
    IntervalIntegrable G volume 0 b ∧
      (∫ y,f y*p (τ-b) y*k b y)/p τ x-f x=(∫ h in 0..b,G h) := by
  let p := fun t y => ∫ z,Real.exp (ouExponent z (t,y)) ∂μ
  let k := fun h y => gaussianKernel (Real.exp (-h)) (1-Real.exp (-2*h)) y x
  let F := fun h => (∫ y,f y*p (τ-h) y*k h y)/p τ x
  let G := fun h => (∫ y,p (τ-h) y*reverseTest (p (τ-h)) f y*k h y)/p τ x
  have hD (h : ℝ) (hh : h∈Ioc 0 b) : HasDerivAt F (G h) h := by
    simpa only [sub_zero] using reverse_ou_kernel_derivative μ f hf hfc τ 0 h hh.1
      (lt_of_le_of_lt hh.2 hbτ) x
  have hlim : Tendsto F (𝓝[>] (0:ℝ)) (𝓝 (f x)) :=
    reverse_kernel_lower_endpoint μ τ (hb.trans hbτ) x f hf.continuous hfc
  obtain ⟨C,_,hC⟩ := reverse_generator_integral_uniform_bound μ f hf hfc τ b hb hbτ x
  obtain ⟨hi,he⟩ := bounded_derivative_endpoint_integral F G 0 b (f x) C hb hD hC hlim
  exact ⟨hi,he.symm⟩
end Asakura.Chapter9

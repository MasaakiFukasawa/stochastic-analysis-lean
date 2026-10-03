import Chapter12GaussianVectorProjection
import Chapter12FiniteMomentMinkowski

open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Asakura.Chapter12
open Asakura.FullAudit
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

theorem gaussian_projection_sobolev_integrable {n k : ℕ}
    (u : Fin k → Fin (n+1) → GaussianJet (n+1)) (m q : ℕ) (x : Fin (n+1) → ℝ) :
    Integrable (fun z : Fin k → ℝ => gaussianSobolevSum (projectedGaussianField u z) m x^q)
      (Measure.pi (fun _ => gaussianReal 0 1)) := by
  simp only [gaussianSobolevSum,gaussian_derivative_projection_norm]
  exact gaussian_sum_array_norm_power_integrable
    (fun j : Fin (m+1) => fun b : Fin (j.val+1) → Fin (n+1) =>
      gaussianLinearFormJet (fun a => (gaussianDerivativeArray (u a) j b).f x)) q

theorem gaussian_projection_sobolev_moment {n k : ℕ}
    (u : Fin k → Fin (n+1) → GaussianJet (n+1)) (m p : ℕ) (hp : 0<p) (x : Fin (n+1) → ℝ) :
    (∫ z : Fin k → ℝ,gaussianSobolevSum (projectedGaussianField u z) m x^(2*p)
      ∂Measure.pi (fun _ => gaussianReal 0 1)) ≤
      gaussianEvenMoment p * gaussianVectorSobolevSum u m x^(2*p) := by
  letI : Fact (1≤((2*p:ℕ):ℝ≥0∞)) := ⟨by exact_mod_cast (show 1≤2*p by omega)⟩
  let c := (gaussianEvenMoment p)^((2*p:ℕ):ℝ)⁻¹
  have hc : 0≤c := Real.rpow_nonneg (gaussian_even_moment_pos p).le _
  have hcp : c^(2*p)=gaussianEvenMoment p :=
    Real.rpow_inv_natCast_pow (gaussian_even_moment_pos p).le (by omega)
  let f := fun j : Fin (m+1) => fun z : Fin k → ℝ => gaussianDerivativeNorm (projectedGaussianField u z) j x
  have hf (j : Fin (m+1)) : MemLp (f j) (2*p:ℕ) (Measure.pi (fun _ => gaussianReal 0 1)) := by
    have he : f j=gaussianArrayNorm (fun b : Fin (j.val+1) → Fin (n+1) =>
        gaussianLinearFormJet (fun a => (gaussianDerivativeArray (u a) j b).f x)) := by
      funext z
      exact gaussian_derivative_projection_norm u z j x
    rw [he]
    exact polynomial_growth_gaussian_memLp (gaussianArrayNorm_continuous _).measurable
      (gaussianArrayNorm_growth _) _ (ENNReal.natCast_ne_top _)
  have hh := finite_moment_minkowski_bound (Measure.pi (fun _ : Fin k => gaussianReal 0 1))
    (2*p) (by omega) f hf (fun _ _ => Real.sqrt_nonneg _) (fun j : Fin (m+1) => gaussianVectorDerivativeNorm u j x)
    (fun _ => Real.sqrt_nonneg _) c hc (fun j => ?_)
  · simpa only [mul_pow,hcp,f,gaussianSobolevSum,gaussianVectorSobolevSum] using hh
  · rw [mul_pow,hcp]
    exact gaussian_derivative_projection_moment u j p hp x

theorem gaussian_projected_array_joint_continuous {n k : ℕ} {I : Type*} [Fintype I]
    (f : I → Fin k → GaussianJet n) :
    Continuous (fun z : (Fin k → ℝ) × (Fin n → ℝ) =>
      Real.sqrt (∑ i,(∑ a,(f i a).f z.2*z.1 a)^2)) := by
  apply Continuous.sqrt
  apply continuous_finset_sum
  intro i _
  apply Continuous.pow
  apply continuous_finset_sum
  intro a _
  exact ((f i a).smooth.continuous.comp continuous_snd).mul ((continuous_apply a).comp continuous_fst)

theorem gaussian_projection_sobolev_joint_continuous {n k : ℕ}
    (u : Fin k → Fin (n+1) → GaussianJet (n+1)) (m : ℕ) :
    Continuous (fun z : (Fin k → ℝ) × (Fin (n+1) → ℝ) =>
      gaussianSobolevSum (projectedGaussianField u z.1) m z.2) := by
  simp only [gaussianSobolevSum,gaussian_derivative_projection_norm]
  exact continuous_finset_sum _ (fun j _ => gaussian_projected_array_joint_continuous
    (fun b a => gaussianDerivativeArray (u a) j b))

end Asakura.Chapter12

import Chapter12GaussianNormIntegrability
import Chapter12GaussianMatrixMoment

open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2300000

noncomputable def projectedGaussianField {n k : ℕ}
    (u : Fin k → Fin (n+1) → GaussianJet (n+1)) (z : Fin k → ℝ) : Fin (n+1) → GaussianJet (n+1) :=
  fun i => gaussianJetProjection (fun a => u a i) z

noncomputable def gaussianVectorDerivativeNorm {n k : ℕ}
    (u : Fin k → Fin (n+1) → GaussianJet (n+1)) (j : ℕ) : (Fin (n+1) → ℝ) → ℝ :=
  gaussianArrayNorm (fun b : Fin k × (Fin (j+1) → Fin (n+1)) => gaussianDerivativeArray (u b.1) j b.2)

noncomputable def gaussianVectorSobolevSum {n k : ℕ}
    (u : Fin k → Fin (n+1) → GaussianJet (n+1)) (m : ℕ) (x : Fin (n+1) → ℝ) : ℝ :=
  ∑ j : Fin (m+1),gaussianVectorDerivativeNorm u j x

theorem gaussian_derivative_projection {n k : ℕ}
    (u : Fin k → Fin (n+1) → GaussianJet (n+1)) (z : Fin k → ℝ) (j : ℕ)
    (b : Fin (j+1) → Fin (n+1)) :
    gaussianDerivativeArray (projectedGaussianField u z) j b=
      gaussianJetProjection (fun a => gaussianDerivativeArray (u a) j b) z :=
  gaussianJetProjection_iteratedPartial (fun a => u a (b 0)) z (List.ofFn (fun i : Fin j => b i.succ))

theorem gaussian_derivative_projection_norm {n k : ℕ}
    (u : Fin k → Fin (n+1) → GaussianJet (n+1)) (z : Fin k → ℝ) (j : ℕ) (x : Fin (n+1) → ℝ) :
    gaussianDerivativeNorm (projectedGaussianField u z) j x=
      Real.sqrt (∑ b : Fin (j+1) → Fin (n+1),
        (∑ a,(gaussianDerivativeArray (u a) j b).f x*z a)^2) := by
  simp only [gaussianDerivativeNorm,gaussianArrayNorm,gaussian_derivative_projection,gaussianJetProjection_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  congr 1
  exact Finset.sum_congr rfl (fun a _ => mul_comm _ _)

theorem gaussian_derivative_projection_moment {n k : ℕ}
    (u : Fin k → Fin (n+1) → GaussianJet (n+1)) (j p : ℕ) (hp : 0<p) (x : Fin (n+1) → ℝ) :
    (∫ z : Fin k → ℝ,gaussianDerivativeNorm (projectedGaussianField u z) j x^(2*p)
      ∂Measure.pi (fun _ => gaussianReal 0 1)) ≤
      gaussianEvenMoment p * gaussianVectorDerivativeNorm u j x^(2*p) := by
  simp only [gaussian_derivative_projection_norm]
  have hh := gaussian_matrix_even_moment
    (fun b (a : Fin k) => (gaussianDerivativeArray (u a) j b).f x) p hp
  have he : (∑ b : Fin (j+1) → Fin (n+1),∑ a : Fin k,(gaussianDerivativeArray (u a) j b).f x^2)=
      ∑ ab : Fin k × (Fin (j+1) → Fin (n+1)),(gaussianDerivativeArray (u ab.1) j ab.2).f x^2 := by
    rw [Fintype.sum_prod_type]
    exact Finset.sum_comm
  rw [he] at hh
  exact hh

theorem gaussian_derivative_projection_power_integrable {n k : ℕ}
    (u : Fin k → Fin (n+1) → GaussianJet (n+1)) (j q : ℕ) (x : Fin (n+1) → ℝ) :
    Integrable (fun z : Fin k → ℝ => gaussianDerivativeNorm (projectedGaussianField u z) j x^q)
      (Measure.pi (fun _ => gaussianReal 0 1)) := by
  simp only [gaussian_derivative_projection_norm]
  exact gaussian_matrix_norm_power_integrable (fun b a => (gaussianDerivativeArray (u a) j b).f x) q

end Asakura.Chapter12

import Chapter12GaussianLinearScoreLaw
import Chapter12GaussianArrayNorm

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

noncomputable def gaussianEvenMoment (p : ℕ) : ℝ :=
  ∫ x : ℝ,x^(2*p) ∂gaussianReal 0 1

/-- Gaussian scalar projection recovers the even power of a Hilbert
coordinate norm with a constant depending only on the moment order. -/
theorem gaussian_projection_even_moment {n : ℕ} (q : Fin n → ℝ) (p : ℕ) :
    (∫ z : Fin n → ℝ,(∑ i,q i*z i)^(2*p) ∂Measure.pi (fun _ => gaussianReal 0 1)) =
      gaussianEvenMoment p * (Real.sqrt (∑ i,q i^2))^(2*p) := by
  let v : ℝ≥0 := ⟨∑ i,q i^2,Finset.sum_nonneg (fun i _ => sq_nonneg _)⟩
  let c := Real.sqrt (v:ℝ)
  have hc : c^2=(v:ℝ) := Real.sq_sqrt v.property
  have hs := gaussianReal_const_mul (HasLaw.id (μ:=gaussianReal 0 1)) c
  have hv : NNReal.mk (c^2) (sq_nonneg c) * (1 : NNReal) = v := by
    apply Subtype.ext
    simpa using hc
  simp only [mul_zero,hv] at hs
  have he := hs.integral_comp (f:=fun x : ℝ => x^(2*p)) (by fun_prop)
  have hq := (finite_gaussian_linear_score_law q).integral_comp (f:=fun x : ℝ => x^(2*p)) (by fun_prop)
  simp only [Function.comp_def] at hq he
  rw [hq,←he]
  simp only [id_eq,mul_pow,integral_const_mul]
  exact mul_comm _ _

end Asakura.Chapter12

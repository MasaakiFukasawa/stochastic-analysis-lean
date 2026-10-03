import Chapter8OUGramCovariance

open Matrix MeasureTheory
open scoped BigOperators
namespace Asakura.Chapter9
open Asakura.Chapter8
set_option maxHeartbeats 1800000

/-- Exact covariance on an arbitrary time interval, retaining the final
OU scaling. The innovation variance depends only on elapsed time. -/
theorem ou_increment_projection_variance {d n : ℕ} (σ : Matrix (Fin d) (Fin n) ℝ)
    (v : Fin d → ℝ) (R s : ℝ) :
    Real.exp (-R)^2*(∫ r in s..R,∑ j,(∑ i,v i*(σ i j*Real.exp r))^2)=
      (1-Real.exp (-2*(R-s)))*(v ⬝ᵥ (((1/2:ℝ) • (σ*σᵀ)) *ᵥ v)) := by
  let f := fun r => ∑ j,(∑ i,v i*(σ i j*Real.exp r))^2
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hi := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hf.intervalIntegrable 0 s) (hf.intervalIntegrable s R)
  have hR := ou_projected_convolution_variance σ v R
  have hs := ou_projected_convolution_variance σ v s
  have he : Real.exp (-R)^2=Real.exp (-2*(R-s))*Real.exp (-s)^2 := by
    rw [pow_two,pow_two,←Real.exp_add,←Real.exp_add,←Real.exp_add]
    congr 1
    ring
  have he2 : Real.exp (-2*R)=Real.exp (-2*(R-s))*Real.exp (-2*s) := by
    rw [←Real.exp_add]
    congr 1
    ring
  have hx := congrArg (fun x : ℝ => Real.exp (-2*(R-s))*x) hs
  change Real.exp (-R)^2*(∫ r in s..R,f r)=_
  change Real.exp (-R)^2*(∫ r in 0..R,f r)=_ at hR
  change Real.exp (-2*(R-s))*(Real.exp (-s)^2*(∫ r in 0..s,f r))=_ at hx
  rw [←mul_assoc,←he] at hx
  rw [he2] at hR
  nlinarith [congrArg (fun x : ℝ => Real.exp (-R)^2*x) hi]
end Asakura.Chapter9

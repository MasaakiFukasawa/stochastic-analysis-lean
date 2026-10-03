import Chapter5WeightedSquareCalculus

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter5
open Asakura.Chapter3Complete
set_option maxHeartbeats 1600000

/-- Lift a scalar C³ function to the space coordinate of the clock-space
Ito formula, with its actual first and second Fréchet derivatives. -/
theorem scalar_lift_derivatives (ψ : ℝ → ℝ) (hψ : ContDiff ℝ 3 ψ) (x : Fin 2 → ℝ) :
    fderiv ℝ (fun y : Fin 2 → ℝ => ψ (y 1)) x (Pi.single 0 1) = 0 ∧
    fderiv ℝ (fun y : Fin 2 → ℝ => ψ (y 1)) x (Pi.single 1 1) = deriv ψ (x 1) ∧
    fderiv ℝ (fderiv ℝ (fun y : Fin 2 → ℝ => ψ (y 1))) x
      (Pi.single 1 1) (Pi.single 1 1) = iteratedDeriv 2 ψ (x 1) := by
  have hd (y : Fin 2 → ℝ) := ((hψ.differentiable (by norm_num)).differentiableAt.hasDerivAt (x := y 1)).comp_hasFDerivAt y (hasFDerivAt_apply (𝕜 := ℝ) 1 y)
  simp only [Function.comp_def] at hd
  have hs y : fderiv ℝ (fun z : Fin 2 → ℝ => ψ (z 1)) y (Pi.single 1 1) = deriv ψ (y 1) := by
    rw [(hd y).fderiv]; simp
  refine ⟨?_,hs x,?_⟩
  · rw [(hd x).fderiv]; simp
  · have hc : ContDiff ℝ 3 (fun y : Fin 2 → ℝ => ψ (y 1)) := hψ.comp (by fun_prop)
    rw [← coordinate_gradient_fderiv _ hc 1,show (fun y : Fin 2 → ℝ => fderiv ℝ (fun z : Fin 2 → ℝ => ψ (z 1)) y (Pi.single 1 1)) = (fun y => deriv ψ (y 1)) from funext hs]
    have hψd : ContDiff ℝ 2 (deriv ψ) := ContDiff.deriv' hψ
    have hdd := ((hψd.differentiable (by norm_num)).differentiableAt.hasDerivAt (x := x 1)).comp_hasFDerivAt x (hasFDerivAt_apply (𝕜 := ℝ) 1 x)
    simp only [Function.comp_def] at hdd
    rw [hdd.fderiv,iteratedDeriv_succ,iteratedDeriv_one]
    simp

end Asakura.Chapter5

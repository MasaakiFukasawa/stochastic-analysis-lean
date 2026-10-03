import Chapter5TimeSpaceDrift
import Chapter3GradientCalculus

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

noncomputable def weightedSquare (β : ℝ) (x : Fin 2 → ℝ) : ℝ := Real.exp (β*x 0)*(x 1)^2

theorem weightedSquare_smooth (β : ℝ) : ContDiff ℝ 3 (weightedSquare β) := by
  unfold weightedSquare
  fun_prop

theorem weightedSquare_fderiv (β : ℝ) (x h : Fin 2 → ℝ) :
    fderiv ℝ (weightedSquare β) x h =
      β*Real.exp (β*x 0)*(x 1)^2*h 0 + 2*Real.exp (β*x 0)*x 1*h 1 := by
  have h0 := (hasFDerivAt_apply (𝕜 := ℝ) 0 x).const_mul β
  have hx := hasFDerivAt_apply (𝕜 := ℝ) 1 x
  have hh := h0.exp.mul (hx.pow 2)
  simp only [Pi.mul_def] at hh
  rw [show weightedSquare β = (fun y => Real.exp (β*y 0)*(y 1)^2) from rfl,hh.fderiv]
  simp
  ring

theorem weightedSquare_time_derivative (β : ℝ) (x : Fin 2 → ℝ) :
    fderiv ℝ (weightedSquare β) x (Pi.single 0 1) = β*Real.exp (β*x 0)*(x 1)^2 := by
  rw [weightedSquare_fderiv]
  simp

theorem weightedSquare_space_derivative (β : ℝ) (x : Fin 2 → ℝ) :
    fderiv ℝ (weightedSquare β) x (Pi.single 1 1) = 2*Real.exp (β*x 0)*x 1 := by
  rw [weightedSquare_fderiv]
  simp

theorem weightedSquare_space_second (β : ℝ) (x : Fin 2 → ℝ) :
    fderiv ℝ (fderiv ℝ (weightedSquare β)) x (Pi.single 1 1) (Pi.single 1 1) = 2*Real.exp (β*x 0) := by
  rw [← coordinate_gradient_fderiv _ (weightedSquare_smooth β) 1]
  have he : (fun y => fderiv ℝ (weightedSquare β) y (Pi.single 1 1)) =
      (fun y => 2*Real.exp (β*y 0)*y 1) := funext (weightedSquare_space_derivative β)
  rw [he]
  have hh := (((hasFDerivAt_apply (𝕜 := ℝ) 0 x).const_mul β).exp.const_mul 2).mul
    (hasFDerivAt_apply (𝕜 := ℝ) 1 x)
  simp only [Pi.mul_def] at hh
  rw [hh.fderiv]
  simp

end Asakura.Chapter5

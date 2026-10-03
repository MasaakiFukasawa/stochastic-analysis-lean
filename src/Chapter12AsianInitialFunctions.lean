import Chapter12AsianVolatilityFunctions

open MeasureTheory Set
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

theorem asian_path_average_linear_initial (x r T σ : ℝ) (hT : 0 ≤ T)
    (f : C(Icc (0:ℝ) T,ℝ)) :
    asianPathAverage x r T hT σ f = x*asianPathAverage 1 r T hT σ f := by
  simp only [asianPathAverage,intervalIntegral.integral_const_mul,one_mul,mul_div_assoc]

theorem asian_path_initial_derivative (x r T σ : ℝ) (hT : 0 ≤ T)
    (f : C(Icc (0:ℝ) T,ℝ)) :
    HasDerivAt (fun a => asianPathAverage a r T hT σ f) (asianPathAverage 1 r T hT σ f) x := by
  have he : (fun a => asianPathAverage a r T hT σ f) =
      fun a => a*asianPathAverage 1 r T hT σ f := funext fun a => asian_path_average_linear_initial a r T σ hT f
  rw [he]
  convert (hasDerivAt_id x).mul_const (asianPathAverage 1 r T hT σ f) using 1 <;> simp

theorem asian_path_initial_lipschitz (r T σ : ℝ) (hT : 0 ≤ T)
    (f : C(Icc (0:ℝ) T,ℝ)) :
    LipschitzWith (Real.nnabs (asianPathAverage 1 r T hT σ f))
      (fun a => asianPathAverage a r T hT σ f) := by
  apply lipschitzWith_iff_dist_le_mul.mpr
  intro a b
  rw [asian_path_average_linear_initial a r T σ hT f,asian_path_average_linear_initial b r T σ hT f]
  simp only [Real.dist_eq,Real.coe_nnabs,←sub_mul,abs_mul]
  exact le_of_eq (mul_comm _ _)

end Asakura.Chapter12

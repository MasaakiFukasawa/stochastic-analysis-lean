import Chapter12CompactTimeMeasure
import Chapter12AsianVolatilityFunctions

open MeasureTheory Set
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

/-- Compact-time Bochner constructions and the interval integrals printed
in the text agree; the clamping disappears on the integration interval. -/
theorem compact_asian_moment (T : ℝ) (hT : 0 ≤ T)
    (f : C(Icc (0:ℝ) T,ℝ)) (x σ r : ℝ) (j : ℕ) :
    (∫ t : Icc (0:ℝ) T,t.val^j*stockPathValue x σ r T f t ∂compactTimeMeasure T hT) =
    ∫ t in 0..T,t^j*(x*Real.exp ((r-σ^2/2)*t+σ*f (projIcc 0 T hT t))) := by
  let a := fun t : ℝ => t^j*(x*Real.exp ((r-σ^2/2)*t+σ*f (projIcc 0 T hT t)))
  have hc : Continuous a := by unfold a; fun_prop
  have he := compact_time_integral T hT a hc.continuousOn
  have hp (t : Icc (0:ℝ) T) : a t.val = t.val^j*stockPathValue x σ r T f t := by
    simp only [a,stockPathValue,projIcc_val]
  simpa only [hp] using he

theorem compact_asian_vega_moment (T : ℝ) (hT : 0 ≤ T)
    (f : C(Icc (0:ℝ) T,ℝ)) (x σ r : ℝ) (j : ℕ) :
    (∫ t : Icc (0:ℝ) T,t.val^j*stockPathValue x σ r T f t*(f t-σ*t.val) ∂compactTimeMeasure T hT) =
    ∫ t in 0..T,t^j*(x*Real.exp ((r-σ^2/2)*t+σ*f (projIcc 0 T hT t)))*(f (projIcc 0 T hT t)-σ*t) := by
  let a := fun t : ℝ => t^j*(x*Real.exp ((r-σ^2/2)*t+σ*f (projIcc 0 T hT t)))*(f (projIcc 0 T hT t)-σ*t)
  have hc : Continuous a := by unfold a; fun_prop
  have he := compact_time_integral T hT a hc.continuousOn
  have hp (t : Icc (0:ℝ) T) : a t.val = t.val^j*stockPathValue x σ r T f t*(f t-σ*t.val) := by
    simp only [a,stockPathValue,projIcc_val]
  simpa only [hp] using he

theorem compact_asian_average (T : ℝ) (hT : 0 < T)
    (f : C(Icc (0:ℝ) T,ℝ)) (x σ r : ℝ) :
    (∫ t : Icc (0:ℝ) T,stockPathValue x σ r T f t ∂compactTimeMeasure T hT.le)/T =
      asianPathAverage x r T hT.le σ f := by
  have he := compact_asian_moment T hT.le f x σ r 0
  simp only [pow_zero,one_mul] at he
  unfold asianPathAverage
  rw [he]

end Asakura.Chapter12

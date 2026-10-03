import Chapter12AsianWeights
import Chapter9CompactParameterDerivative
import Chapter12AsianDenominatorBound

open MeasureTheory Set
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- Differentiate the pathwise time integral with respect to volatility.
Compactness in time supplies the local domination needed for the exchange. -/
theorem asian_time_moment_volatility_derivative (x r σ T : ℝ) (hT : 0 ≤ T)
    (f : C(Icc (0:ℝ) T,ℝ)) (j : ℕ) :
    HasDerivAt (fun a : ℝ => ∫ s in 0..T,
      s^j*(x*Real.exp ((r-a^2/2)*s+a*f (projIcc 0 T hT s))))
      (∫ s in 0..T,s^j*(x*Real.exp ((r-σ^2/2)*s+σ*f (projIcc 0 T hT s)))*
        (f (projIcc 0 T hT s)-σ*s)) σ := by
  let F := fun a s : ℝ => s^j*(x*Real.exp ((r-a^2/2)*s+a*f (projIcc 0 T hT s)))
  let D := fun a s : ℝ => F a s*(f (projIcc 0 T hT s)-a*s)
  have hF : Continuous F.uncurry := by unfold F; fun_prop
  have hD : Continuous D.uncurry := by unfold D F; fun_prop
  have hd a s : HasDerivAt (fun b => F b s) (D a s) a := by
    have hh := (stock_volatility_derivative x r s (f (projIcc 0 T hT s)) a).const_mul (s^j)
    convert hh using 1
    dsimp only [D,F]
    ring
  have h := Asakura.Chapter9.compact_parameter_integral_derivative
    (volume.restrict (Ioc 0 T)) (Icc 0 T) isCompact_Icc
    ((ae_restrict_mem measurableSet_Ioc).mono (fun _ hs => ⟨hs.1.le,hs.2⟩))
    F D univ isOpen_univ hF.continuousOn hD.continuousOn
    (fun a _ s => hd a s) σ (mem_univ _)
  simpa only [intervalIntegral.integral_of_le hT,F,D] using h

/-- The case j=0 divided by T is the derivative of the arithmetic average
used in the vega direction equation. -/
theorem asian_average_volatility_derivative (x r σ T : ℝ) (hT : 0 ≤ T)
    (f : C(Icc (0:ℝ) T,ℝ)) :
    HasDerivAt (fun a : ℝ => (∫ s in 0..T,
      x*Real.exp ((r-a^2/2)*s+a*f (projIcc 0 T hT s)))/T)
      ((∫ s in 0..T,(x*Real.exp ((r-σ^2/2)*s+σ*f (projIcc 0 T hT s)))*
        (f (projIcc 0 T hT s)-σ*s))/T) σ := by
  simpa only [pow_zero,one_mul] using (asian_time_moment_volatility_derivative x r σ T hT f 0).div_const T

end Asakura.Chapter12

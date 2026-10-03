import Chapter12AsianAverageVegaEnvelope

open MeasureTheory Set
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

noncomputable def asianPathAverage (x r T : ℝ) (hT : 0 ≤ T)
    (σ : ℝ) (f : C(Icc (0:ℝ) T,ℝ)) : ℝ :=
  (∫ s in 0..T,x*Real.exp ((r-σ^2/2)*s+σ*f (projIcc 0 T hT s)))/T

noncomputable def asianPathVega (x r T : ℝ) (hT : 0 ≤ T)
    (σ : ℝ) (f : C(Icc (0:ℝ) T,ℝ)) : ℝ :=
  (∫ s in 0..T,(x*Real.exp ((r-σ^2/2)*s+σ*f (projIcc 0 T hT s)))*
    (f (projIcc 0 T hT s)-σ*s))/T

theorem asian_path_volatility_derivative (x r T : ℝ) (hT : 0 ≤ T)
    (σ : ℝ) (f : C(Icc (0:ℝ) T,ℝ)) :
    HasDerivAt (fun a => asianPathAverage x r T hT a f) (asianPathVega x r T hT σ f) σ :=
  asian_average_volatility_derivative x r σ T hT f

theorem asian_path_average_measurable (x r T : ℝ) (hT : 0 ≤ T) (σ : ℝ) :
    Measurable (asianPathAverage x r T hT σ) := by
  let F := fun z : C(Icc (0:ℝ) T,ℝ) × ℝ =>
    x*Real.exp ((r-σ^2/2)*z.2+σ*z.1 (projIcc 0 T hT z.2))
  have hF : Continuous F := by unfold F; fun_prop
  have hm := (hF.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ioc 0 T))).measurable
  unfold asianPathAverage
  simpa only [intervalIntegral.integral_of_le hT,F] using hm.div_const T

theorem asian_path_vega_measurable (x r T : ℝ) (hT : 0 ≤ T) (σ : ℝ) :
    Measurable (asianPathVega x r T hT σ) := by
  let F := fun z : C(Icc (0:ℝ) T,ℝ) × ℝ =>
    (x*Real.exp ((r-σ^2/2)*z.2+σ*z.1 (projIcc 0 T hT z.2)))*
      (z.1 (projIcc 0 T hT z.2)-σ*z.2)
  have hF : Continuous F := by unfold F; fun_prop
  have hm := (hF.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ioc 0 T))).measurable
  unfold asianPathVega
  simpa only [intervalIntegral.integral_of_le hT,F] using hm.div_const T

theorem asian_path_volatility_lipschitz (x r T L : ℝ) (hT : 0 < T) (hL : 0 ≤ L)
    (f : C(Icc (0:ℝ) T,ℝ)) :
    LipschitzOnWith (Real.nnabs (asianVegaPathEnvelope x r T L f))
      (fun σ => asianPathAverage x r T hT.le σ f) (Icc (-L) L) := by
  apply (convex_Icc (-L) L).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (fun σ _ => (asian_path_volatility_derivative x r T hT.le σ f).hasDerivWithinAt)
  intro σ hσ
  apply NNReal.coe_le_coe.mpr
  change |asianPathVega x r T hT.le σ f| ≤ |asianVegaPathEnvelope x r T L f|
  have hn : 0 ≤ asianVegaPathEnvelope x r T L f := by unfold asianVegaPathEnvelope; positivity
  rw [abs_of_nonneg hn]
  exact asian_average_vega_uniform_bound x r T L σ hT hL (abs_le.mpr hσ) f

end Asakura.Chapter12

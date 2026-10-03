import Chapter12AsianVegaIntegralGraph
import Chapter12AsianMomentGraphs

open MeasureTheory Set
open scoped RealInnerProductSpace
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

noncomputable def asianVegaMoment (T : ℝ) (hT : 0 ≤ T) (x σ r : ℝ) (j : ℕ)
    (f : C(Icc (0:ℝ) T,ℝ)) : ℝ :=
  ∫ t : Icc (0:ℝ) T,t.val^j*stockPathValue x σ r T f t*(f t-σ*t.val) ∂compactTimeMeasure T hT

noncomputable def asianVegaGradient {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (T : ℝ) (hT : 0 ≤ T) (x σ r : ℝ) (h : Icc (0:ℝ) T → H)
    (f : C(Icc (0:ℝ) T,ℝ)) : H :=
  ∫ t : Icc (0:ℝ) T,(stockPathValue x σ r T f t*(σ*(f t-σ*t.val)+1)) • h t ∂compactTimeMeasure T hT

theorem asian_vega_moment_pairing {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    (T : ℝ) (hT : 0 ≤ T) (x σ r : ℝ) (h : Icc (0:ℝ) T → H) (hh : Continuous h)
    (hTdir : H) (hp : ∀ t, inner ℝ (h t) hTdir = t.val) (f : C(Icc (0:ℝ) T,ℝ)) :
    inner ℝ (asianVegaGradient T hT x σ r h f) hTdir =
      σ*asianVegaMoment T hT x σ r 1 f+asianMoment T hT x σ r 1 f := by
  have hc : Continuous (fun t : Icc (0:ℝ) T => stockPathValue x σ r T f t*(σ*(f t-σ*t.val)+1)) := by
    unfold stockPathValue
    fun_prop
  have he := integrated_direction_pairing T hT h hh hTdir hp _ hc 1
  simp only [one_smul,one_mul] at he
  unfold asianVegaGradient asianVegaMoment asianMoment
  rw [he]
  have h1 : Integrable (fun t : Icc (0:ℝ) T => σ*(t.val*stockPathValue x σ r T f t*(f t-σ*t.val))) (compactTimeMeasure T hT) := by
    apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    unfold stockPathValue
    fun_prop
  have h2 : Integrable (fun t : Icc (0:ℝ) T => t.val*stockPathValue x σ r T f t) (compactTimeMeasure T hT) := by
    apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    unfold stockPathValue
    fun_prop
  simp only [pow_one]
  rw [←integral_const_mul,←integral_add h1 h2]
  apply integral_congr_ae
  apply ae_of_all
  intro t
  ring

end Asakura.Chapter12

import Chapter12PrefixTerminalPairing
import Chapter12StockTimeMomentExplicit

open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

/-- The integrated Malliavin derivative of I_j pairs with the constant
Brownian direction to give sigma I_(j+1). This includes j=0,1,2. -/
theorem asian_moment_derivative_pairing {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) (T : ℝ) (hT : 0 ≤ T) (f : C(Icc (0:ℝ) T,ℝ)) (x σ r : ℝ) (j : ℕ) :
    inner ℝ (∫ t : Icc (0:ℝ) T,(t.val^j*stockPathValue x σ r T f t) •
      (σ • singleCoordinateIsometry i (finiteTimeIntervalVector T 0 t.val)) ∂compactTimeMeasure T hT)
      (singleCoordinateIsometry i (finiteTimeIntervalVector T 0 T)) =
    σ * ∫ t : Icc (0:ℝ) T,t.val^(j+1)*stockPathValue x σ r T f t ∂compactTimeMeasure T hT := by
  have hc : Continuous (fun t : Icc (0:ℝ) T => t.val^j*stockPathValue x σ r T f t) := by
    unfold stockPathValue
    fun_prop
  rw [integrated_prefix_terminal_pairing i T hT _ hc σ]
  congr 1
  apply integral_congr_ae
  apply ae_of_all
  intro t
  dsimp only
  rw [pow_succ]
  ring

/-- Pairing the derivative of J_0 gives sigma J_1+I_1; the extra I_1
is responsible for the -1/sigma correction in the Asian vega. -/
theorem asian_vega_derivative_pairing {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) (T : ℝ) (hT : 0 ≤ T) (f : C(Icc (0:ℝ) T,ℝ)) (x σ r : ℝ) :
    inner ℝ (∫ t : Icc (0:ℝ) T,(stockPathValue x σ r T f t * (σ*(f t-σ*t.val)+1)) •
      singleCoordinateIsometry i (finiteTimeIntervalVector T 0 t.val) ∂compactTimeMeasure T hT)
      (singleCoordinateIsometry i (finiteTimeIntervalVector T 0 T)) =
    σ * (∫ t : Icc (0:ℝ) T,t.val*stockPathValue x σ r T f t*(f t-σ*t.val) ∂compactTimeMeasure T hT)+
      ∫ t : Icc (0:ℝ) T,t.val*stockPathValue x σ r T f t ∂compactTimeMeasure T hT := by
  have hc : Continuous (fun t : Icc (0:ℝ) T => stockPathValue x σ r T f t*(σ*(f t-σ*t.val)+1)) := by
    unfold stockPathValue
    fun_prop
  have he := integrated_prefix_terminal_pairing i T hT _ hc 1
  simp only [one_smul,one_mul] at he
  rw [he]
  have h1 : Integrable (fun t : Icc (0:ℝ) T => σ*(t.val*stockPathValue x σ r T f t*(f t-σ*t.val))) (compactTimeMeasure T hT) := by
    apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    unfold stockPathValue
    fun_prop
  have h2 : Integrable (fun t : Icc (0:ℝ) T => t.val*stockPathValue x σ r T f t) (compactTimeMeasure T hT) := by
    apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    unfold stockPathValue
    fun_prop
  rw [←integral_const_mul,←integral_add h1 h2]
  apply integral_congr_ae
  apply ae_of_all
  intro t
  ring

end Asakura.Chapter12

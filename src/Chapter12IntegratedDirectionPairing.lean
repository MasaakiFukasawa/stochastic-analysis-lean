import Chapter12CompactTimeMeasure
import Mathlib.Analysis.InnerProductSpace.LinearMap

open MeasureTheory Set
open scoped RealInnerProductSpace
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

theorem integrated_direction_pairing {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    (T : ℝ) (hT : 0 ≤ T) (h : Icc (0:ℝ) T → H) (hh : Continuous h)
    (hTdir : H) (hp : ∀ t, inner ℝ (h t) hTdir = t.val)
    (a : Icc (0:ℝ) T → ℝ) (ha : Continuous a) (σ : ℝ) :
    inner ℝ (∫ t,a t • (σ • h t) ∂compactTimeMeasure T hT) hTdir =
      σ * ∫ t,t.val*a t ∂compactTimeMeasure T hT := by
  have hi := (ha.smul (hh.const_smul σ)).integrable_of_hasCompactSupport
    (μ := compactTimeMeasure T hT) (HasCompactSupport.of_compactSpace _)
  have he := (innerSL ℝ hTdir).integral_comp_comm hi
  change (∫ t,inner ℝ hTdir (a t • (σ • h t)) ∂compactTimeMeasure T hT) =
    inner ℝ hTdir (∫ t,a t • (σ • h t) ∂compactTimeMeasure T hT) at he
  rw [real_inner_comm] at he
  rw [←he,←integral_const_mul]
  apply integral_congr_ae
  apply ae_of_all
  intro t
  dsimp only
  rw [inner_smul_right,inner_smul_right,real_inner_comm,hp]
  ring

end Asakura.Chapter12

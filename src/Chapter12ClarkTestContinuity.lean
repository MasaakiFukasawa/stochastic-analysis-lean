import Chapter12LpInclusion
import Chapter12FiniteGreekExponents
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.L2Space

open MeasureTheory Set
open scoped ENNReal Topology RealInnerProductSpace
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

/-- L4 convergence of the past test variables suffices in the increment
test: multiplication by the Gaussian increment is continuous into L2. -/
theorem clark_test_isClosed {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F K : Lp ℝ 2 P) (B : Lp ℝ 4 P) :
    IsClosed {G : Lp ℝ 4 P | (∫ w, G w*K w ∂P) = ∫ w, F w*G w*B w ∂P} := by
  let J := probabilityLpInclusion (E := ℝ) P 2 4 (by norm_num)
  let L := (ContinuousLinearMap.mul ℝ ℝ).holderL P 4 4 2
  have hleft (G : Lp ℝ 4 P) : inner ℝ K (J G) = ∫ w, G w*K w ∂P := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [probabilityLpInclusion_coe P 2 4 (by norm_num) G] with w hw
    change J G w * K w = _
    rw [hw]
  have hright (G : Lp ℝ 4 P) : inner ℝ F (L G B) = ∫ w, F w*G w*B w ∂P := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(ContinuousLinearMap.mul ℝ ℝ).coeFn_holder (r := 2) G B] with w hw
    simp only [L,ContinuousLinearMap.holderL_apply_apply]
    rw [hw]
    change (G w*B w)*F w = _
    ring
  have hc : IsClosed {G : Lp ℝ 4 P | inner ℝ K (J G) = inner ℝ F (L G B)} :=
    isClosed_eq ((innerSL ℝ K).continuous.comp J.continuous)
      ((innerSL ℝ F).continuous.comp (L.continuous₂.comp (continuous_id.prodMk continuous_const)))
  simpa only [hleft,hright] using hc

end Asakura.Chapter12

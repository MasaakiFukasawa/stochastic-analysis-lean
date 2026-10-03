import Chapter12AsianAverageVegaEnvelope
import Chapter12InverseMomentsTrim

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

theorem asian_vega_envelope_on_trim {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ)
    (hB : IsPreBrownianReal B P) (hm : ∀ t, Measurable (B t))
    (hc : ∀ w, Continuous (fun t => B t w)) (T : ℝ≥0)
    (mT : MeasurableSpace Ω) (hle : mT ≤ m)
    (X : Ω → C(Icc (0:ℝ) T,ℝ)) (hXm : Measurable[mT] X)
    (he : ∀ w (s : Icc (0:ℝ) T), X w s = B ⟨s.val,s.property.1⟩ w)
    (x σ r : ℝ) (p : ℝ≥0∞) (hp : p ≠ ⊤) :
    ∃ G : Ω → ℝ, MemLp G p (P.trim hle) ∧
      ∀ t : Icc (0:ℝ) T, ∀ w,
        ‖stockPathValue x σ r T (X w) t*(X w t-σ*t.val)‖ ≤ ‖G w‖ := by
  letI : MeasurableSpace Ω := m
  let G := fun w => asianVegaPathEnvelope x r T |σ| (X w)
  have hG : MemLp G p P := asian_vega_envelope_memLp P B hB hm hc T X (hXm.mono hle le_rfl) he x r |σ| p hp
  have hGt : MemLp G p (P.trim hle) := by
    apply memLp_on_trim P mT hle G p _ hG
    letI : MeasurableSpace Ω := mT
    unfold G asianVegaPathEnvelope
    exact (((hXm.norm.const_mul (|σ| +1)).exp).const_mul _).stronglyMeasurable
  refine ⟨G,hGt,fun t w => ?_⟩
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (show 0 ≤ G w by unfold G asianVegaPathEnvelope; positivity)]
  exact stock_volatility_derivative_uniform_bound x r T |σ| σ T.property (abs_nonneg _) le_rfl (X w) t

end Asakura.Chapter12

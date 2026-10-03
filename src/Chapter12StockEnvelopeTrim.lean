import Chapter12StockPathEnvelope
import Mathlib.MeasureTheory.Function.LpSeminorm.Trim

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

/-- Restricting information at T preserves the stock path envelope moments.
No Brownian increments after T are postulated on the smaller sigma algebra. -/
theorem stock_path_envelope_on_trim {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (mT : MeasurableSpace Ω) (hle : mT ≤ m)
    (B : ℝ≥0 → Ω → ℝ) (hB : IsPreBrownianReal B P)
    (hm : ∀ t, Measurable[m] (B t)) (hc : ∀ w, Continuous (fun t => B t w))
    (T : ℝ≥0) (X : Ω → C(Icc (0:ℝ) T,ℝ)) (hXm : Measurable[mT] X)
    (he : ∀ w (s : Icc (0:ℝ) T), X w s = B ⟨s.val,s.property.1⟩ w)
    (x σ r : ℝ) (p : ℝ≥0∞) (hp : p ≠ ⊤) :
    ∃ G : Ω → ℝ, MemLp G p (P.trim hle) ∧
      (∀ t : Icc (0:ℝ) T, ∀ w, ‖stockPathValue x σ r T (X w) t‖ ≤ ‖G w‖) ∧
      ∀ t : Icc (0:ℝ) T, MemLp (fun w => stockPathValue x σ r T (X w) t) p (P.trim hle) := by
  letI : MeasurableSpace Ω := m
  let G := fun w => (|x| * Real.exp (|r-σ^2/2| *T)) * Real.exp (|σ| *‖X w‖)
  have hG : MemLp G p P :=
    (brownian_path_exponential_memLp P B hB hm hc T X (hXm.mono hle le_rfl) he |σ| p hp).const_mul _
  letI : MeasurableSpace Ω := mT
  have hGm : StronglyMeasurable[mT] G := by
    exact (((hXm.norm.const_mul |σ|).exp).const_mul _).stronglyMeasurable
  have hGt : MemLp G p (P.trim hle) := by
    change eLpNorm G p (P.trim hle) < ⊤
    rw [eLpNorm_trim hle hGm]
    exact hG.eLpNorm_lt_top
  have hb (t : Icc (0:ℝ) T) (w : Ω) : ‖stockPathValue x σ r T (X w) t‖ ≤ ‖G w‖ := by
    rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (show 0 ≤ G w by dsimp [G]; positivity)]
    dsimp only [G]
    rw [mul_assoc,← Real.exp_add]
    exact stock_path_upper_bound x σ r T (X w) t
  refine ⟨G,hGt,hb,fun t => ?_⟩
  apply hGt.of_le
  · exact ((stock_path_joint_measurable x σ r T X hXm).comp measurable_prodMk_left).aestronglyMeasurable
  · exact ae_of_all (P.trim hle) (hb t)

end Asakura.Chapter12

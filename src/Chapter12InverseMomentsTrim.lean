import Chapter12AsianInverseMoments
import Mathlib.MeasureTheory.Function.LpSeminorm.Trim

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

theorem memLp_on_trim {Ω E : Type*} [m : MeasurableSpace Ω]
    [NormedAddCommGroup E] (P : Measure Ω) (mT : MeasurableSpace Ω) (hle : mT ≤ m)
    (f : Ω → E) (p : ℝ≥0∞) (hm : StronglyMeasurable[mT] f) (hf : MemLp f p P) :
    MemLp f p (P.trim hle) := by
  change eLpNorm f p (P.trim hle) < ⊤
  rw [eLpNorm_trim hle hm]
  exact hf

theorem asian_inverse_moments_on_trim {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ)
    (hB : IsPreBrownianReal B P) (hm : ∀ t, Measurable (B t))
    (hc : ∀ w, Continuous (fun t => B t w)) (T : ℝ≥0) (hT : 0 < T)
    (mT : MeasurableSpace Ω) (hle : mT ≤ m)
    (X : Ω → C(Icc (0:ℝ) T,ℝ)) (hXm : Measurable[mT] X)
    (he : ∀ w (s : Icc (0:ℝ) T), X w s = B ⟨s.val,s.property.1⟩ w)
    (x σ r : ℝ) (hx : 0 < x) (p : ℝ≥0∞) (hp : p ≠ ⊤) :
    MemLp (fun w => (asianFirstTimeMoment x σ r T (show 0 ≤ (T:ℝ) from hT.le) (X w))⁻¹)
      p (P.trim hle) := by
  letI : MeasurableSpace Ω := m
  have hi := asian_first_time_inverse_memLp P B hB hm hc T hT X (hXm.mono hle le_rfl) he x σ r hx p hp
  apply memLp_on_trim P mT hle _ p _ hi
  letI : MeasurableSpace Ω := mT
  exact (((asianFirstTimeMoment_measurable x σ r T (show 0 ≤ (T:ℝ) from hT.le)).comp hXm).inv).stronglyMeasurable

end Asakura.Chapter12

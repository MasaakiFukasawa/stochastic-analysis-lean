import Chapter12AsianCallDeltaExchange
import Chapter12InverseMomentsTrim

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

/-- Atomlessness is preserved when restricting to terminal information,
because the Asian average is measurable for that information. -/
theorem asian_average_no_atom_on_trim {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ)
    (hB : IsPreBrownianReal B P) (hm : ∀ t, Measurable (B t))
    (hc : ∀ w, Continuous (fun t => B t w)) (T : ℝ≥0) (hT : 0 < T)
    (mT : MeasurableSpace Ω) (hle : mT ≤ m)
    (X : Ω → C(Icc (0:ℝ) T,ℝ)) (hXm : Measurable[mT] X)
    (he : ∀ w (s : Icc (0:ℝ) T), X w s = B ⟨s.val,s.property.1⟩ w)
    (x σ r K : ℝ) (hx : 0 < x) (hσ : 0 < σ) :
    (P.trim hle) {w | asianPathAverage x r T T.property σ (X w) = K} = 0 := by
  letI : MeasurableSpace Ω := m
  have hno : P {w | asianPathAverage x r T T.property σ (X w) = K} = 0 :=
    brownian_arithmetic_average_no_atom P B hB x σ r T hx hσ hT X (hXm.mono hle le_rfl)
      (brownian_path_memLp P B hB hm hc T X (hXm.mono hle le_rfl) he 2 (by simp)) he K
  rw [trim_measurableSet_eq hle]
  · exact hno
  · letI : MeasurableSpace Ω := mT
    exact measurableSet_eq_fun ((asian_path_average_measurable x r T T.property σ).comp hXm) measurable_const

end Asakura.Chapter12

import Chapter8BoundedExpectationC2

open MeasureTheory Set
namespace Asakura.Chapter8
set_option maxHeartbeats 1100000
set_option backward.isDefEq.respectTransparency false

/-- Continuity of expected generator values under a pathwise integrable
bound. Linear growth is sufficient; the generator need not be bounded. -/
theorem generator_expectation_continuous {E Ω : Type*}
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω]
    (P : Measure Ω) (T : ℝ) (X : Icc (0:ℝ) T → Ω → E)
    (hXm : ∀ t,Measurable (X t)) (hXc : ∀ᵐ ω ∂P,Continuous (fun t => X t ω))
    (R : Ω → ℝ) (hR : Integrable R P)
    (hXb : ∀ᵐ ω ∂P,∀ t,‖X t ω‖ ≤ R ω)
    (H : E → ℝ) (hH : Continuous H) (C : ℝ) (hC : 0 ≤ C)
    (hHb : ∀ x,‖H x‖ ≤ C*(1+‖x‖)) [IsFiniteMeasure P] :
    Continuous (fun t => ∫ ω,H (X t ω) ∂P) := by
  apply continuous_of_dominated (bound := fun ω => C*(1+R ω))
  · intro t
    exact (hH.measurable.comp (hXm t)).aestronglyMeasurable
  · intro t
    filter_upwards [hXb] with ω hω
    exact (hHb _).trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl (hω t)) hC)
  · exact ((integrable_const (1:ℝ)).add hR).const_mul C
  · exact hXc.mono (fun ω hω => hH.comp hω)

end Asakura.Chapter8

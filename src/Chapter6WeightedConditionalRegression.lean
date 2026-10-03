import Chapter6FiniteGaussianRegression
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter6
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

/-- Condition first on the intermediate point and endpoint, pull out
the bounded coefficient, and then condition on the endpoint using C5. -/
theorem weighted_conditional_regression {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (G H : MeasurableSpace Ω) (hGH : G≤H) (hH : H≤m)
    (X Y b : Ω → ℝ) (hX : Integrable X P) (hb : Measurable[H] b)
    (K : ℝ) (hbb : ∀ᵐ w ∂P,‖b w‖≤K) (he : P[X|H]=ᵐ[P] Y) :
    P[(fun w => b w*X w)|G]=ᵐ[P] P[(fun w => b w*Y w)|G] := by
  have hp := condExp_stronglyMeasurable_mul_of_bound hH hb.stronglyMeasurable hX K hbb
  have hm : P[(fun w => b w*X w)|H]=ᵐ[P] fun w => b w*Y w := by
    filter_upwards [hp,he] with w hp he
    change P[(fun w => b w*X w)|H] w=b w*P[X|H] w at hp
    rw [hp,he]
  have ht := condExp_condExp_of_le hGH hH (f := fun w => b w*X w) (μ := P)
  exact ht.symm.trans (condExp_congr_ae hm)

end Asakura.Chapter6

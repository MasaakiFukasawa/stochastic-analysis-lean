import Chapter4ShiftedCovariance
import Chapter2LocalNonnegative

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- Equality follows from the three actual covariances, by the zero-square
local martingale argument. -/
theorem local_equal_of_three_covariances
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)]
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (X Y A B C : ClosedTime T → Ω → ℝ)
    (hX : LocalMProcessWitness P F X) (hY : LocalMProcessWitness P F Y)
    (hA : LocalCovarianceWitness P F X X A) (hB : LocalCovarianceWitness P F Y Y B)
    (hC : LocalCovarianceWitness P F X Y C)
    (he : ∀ᵐ w ∂P,∀ t,t<⊤ → A t w+B t w-2*C t w=0) :
    ∀ᵐ w ∂P,∀ t,t<⊤ → X t w=Y t w := by
  have hh := ((hA.defect.add P F hF hle hB.defect).add P F hF hle (hC.defect.smul P F (-2)))
  have hsq : LocalMProcessWitness P F (fun t w => (X t w-Y t w)^2) := by
    apply Asakura.Chapter3Complete.LocalMProcessWitness.congr_ae_open P F hF hh
    · intro t ht
      exact ((hX.adapted P F t ht).sub (hY.adapted P F t ht)).pow_const 2
    · intro w t ht
      exact ((hX.path P F w t ht).sub (hY.path P F w t ht)).pow 2
    · filter_upwards [he] with w hw
      intro t ht
      change X t w*X t w-A t w+(Y t w*Y t w-B t w)+(-2)*(X t w*Y t w-C t w)=(X t w-Y t w)^2
      nlinarith [hw t ht]
  exact (local_square_martingale_zero P F hF hle _ hsq).mono
    (fun w hw t ht => sub_eq_zero.mp (hw t ht))

end Asakura.Chapter4

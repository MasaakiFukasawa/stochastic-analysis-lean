import Chapter3BDG

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

/-- Positive constants in precisely the orientation printed in the manuscript. -/
theorem bdg_original_constants_positive (p : ℝ) (hp : 0 < p) :
    0 < 1/(bdgUpperMomentConstant p^(1/p)) ∧ 0 < bdgReverseMomentConstant p^(1/p) := by
  have h := bdg_moment_constants_positive p hp
  constructor
  · exact one_div_pos.mpr (Real.rpow_pos_of_pos h.1 _)
  · exact Real.rpow_pos_of_pos h.2 _

theorem bdg_original_inequality
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X A : ClosedTime T → Ω → ℝ)
    (hX : LocalMProcessWitness P F X) (hA : LocalCovarianceWitness P F X X A)
    (p : ℝ) (hp : 0 < p) (b : ClosedTime T) (hb : b < ⊤) :
    ENNReal.ofReal (1/(bdgUpperMomentConstant p^(1/p)))*
        eLpNorm (runningMaximum X (hX.path P F) b) (ENNReal.ofReal p) P ≤
      eLpNorm (fun ω => Real.sqrt (A b ω)) (ENNReal.ofReal p) P ∧
    eLpNorm (fun ω => Real.sqrt (A b ω)) (ENNReal.ofReal p) P ≤
      ENNReal.ofReal (bdgReverseMomentConstant p^(1/p))*
        eLpNorm (runningMaximum X (hX.path P F) b) (ENNReal.ofReal p) P := by
  have h := bdg_norms P hT F hF hle hnull X A hX hA p hp b hb
  refine ⟨?_,h.2⟩
  have hpos : 0 < bdgUpperMomentConstant p^(1/p) :=
    Real.rpow_pos_of_pos (bdg_moment_constants_positive p hp).1 _
  rw [one_div,ENNReal.ofReal_inv_of_pos hpos]
  have hh := mul_le_mul' (le_refl (ENNReal.ofReal (bdgUpperMomentConstant p^(1/p)))⁻¹) h.1
  rw [← mul_assoc,ENNReal.inv_mul_cancel (by exact ne_of_gt (ENNReal.ofReal_pos.mpr hpos)) ENNReal.ofReal_ne_top,one_mul] at hh
  exact hh

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.bdg_original_constants_positive
#print axioms Asakura.Chapter3Complete.bdg_original_inequality

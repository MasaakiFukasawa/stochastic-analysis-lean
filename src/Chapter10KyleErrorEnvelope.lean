import FullAuditMartingalePathNorm

open MeasureTheory Set Filter
namespace Asakura.Chapter10
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option backward.isDefEq.respectTransparency false

/-- The price path bound furnished by Doob supplies the actual error
envelope required to show the profit's stochastic integral is in M2. -/
theorem kyle_error_envelope {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {T : EReal} [Fact (0≤T)]
    (p : Ω → C(ClosedTime T,ℝ)) (V : Ω → ℝ)
    (hp : MemLp p 2 P) (hV : MemLp V 2 P) :
    ∃ K : Ω → ℝ,MemLp K 2 P ∧ ∀ w t,‖V w-p w t‖≤‖K w‖ := by
  refine ⟨(fun w => ‖V w‖+‖p w‖),hV.norm.add hp.norm,?_⟩
  intro w t
  rw [Real.norm_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
  exact (norm_sub_le _ _).trans (add_le_add_right ((p w).norm_coe_le_norm t) _)

end Asakura.Chapter10

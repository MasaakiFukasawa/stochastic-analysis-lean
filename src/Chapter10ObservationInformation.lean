import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Tactic.FieldSimp

open MeasureTheory
namespace Asakura.Chapter10
set_option backward.isDefEq.respectTransparency false

/-- Pointwise invertible deterministic rescaling preserves the full observation
history, including when the index set is an entire real-time interval. -/
theorem affine_history_information {Ω ι : Type*}
    (Y : ι → Ω → ℝ) (a b : ι → ℝ) (hb : ∀ i,b i≠0) :
    MeasurableSpace.comap (fun w i => a i+b i*Y i w) inferInstance =
      MeasurableSpace.comap (fun w i => Y i w) inferInstance := by
  apply le_antisymm
  · letI : MeasurableSpace Ω :=
      MeasurableSpace.comap (fun w i => Y i w) inferInstance
    apply Measurable.comap_le
    apply Measurable.of_eval
    intro i
    have hm : Measurable (fun w => Y i w) :=
      (measurable_pi_apply i).comp (show Measurable (fun w i => Y i w) from Measurable.of_comap_le le_rfl)
    exact measurable_const.add (measurable_const.mul hm)
  · letI : MeasurableSpace Ω :=
      MeasurableSpace.comap (fun w i => a i+b i*Y i w) inferInstance
    apply Measurable.comap_le
    apply Measurable.of_eval
    intro i
    have hm : Measurable (fun w => a i+b i*Y i w) :=
      (measurable_pi_apply i).comp (show Measurable (fun w i => a i+b i*Y i w) from Measurable.of_comap_le le_rfl)
    have hr := (hm.sub_const (a i)).div_const (b i)
    simpa only [add_sub_cancel_left, mul_div_cancel_left₀ _ (hb i)] using hr

end Asakura.Chapter10

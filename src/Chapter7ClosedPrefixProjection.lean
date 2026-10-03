import Chapter7ClockHalfTime

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

noncomputable def closedPrefixProjection (R : ℝ) [Fact (0 ≤ (R:EReal))]
    (t : HalfClosedTime) : ClosedTime (R:EReal) :=
  ⟨min t.val (R:EReal),le_min t.property.1 (Fact.out),min_le_right _ _⟩

def closedPrefixInclusion (R : ℝ) [Fact (0 ≤ (R:EReal))]
    (t : ClosedTime (R:EReal)) : HalfClosedTime := ⟨t.val,t.property.1,le_top⟩

lemma closed_prefix_projection_mono (R : ℝ) [Fact (0 ≤ (R:EReal))] :
    Monotone (closedPrefixProjection R) := by
  intro s t h
  change min s.val (R:EReal) ≤ min t.val (R:EReal)
  exact min_le_min_right _ h
lemma closed_prefix_projection_continuous (R : ℝ) [Fact (0 ≤ (R:EReal))] :
    Continuous (closedPrefixProjection R) :=
  (continuous_subtype_val.min continuous_const).subtype_mk _
lemma closed_prefix_projection_inclusion (R : ℝ) [Fact (0 ≤ (R:EReal))]
    (t : ClosedTime (R:EReal)) : closedPrefixProjection R (closedPrefixInclusion R t) = t := by
  apply Subtype.ext
  exact min_eq_left t.property.2
lemma closed_prefix_projection_bot (R : ℝ) [Fact (0 ≤ (R:EReal))] :
    closedPrefixProjection R ⊥ = ⊥ := by
  apply Subtype.ext
  exact min_eq_left (Fact.out)
lemma closed_prefix_projection_le_iff (R : ℝ) [Fact (0 ≤ (R:EReal))]
    (s : HalfClosedTime) (t : ClosedTime (R:EReal)) (ht : t < ⊤) :
    closedPrefixProjection R s ≤ t ↔ s ≤ closedPrefixInclusion R t := by
  change min s.val (R:EReal) ≤ t.val ↔ s.val ≤ t.val
  have hrt : ¬(R:EReal) ≤ t.val := not_le_of_gt ht
  simp only [min_le_iff,hrt,or_false]

lemma closed_prefix_projection_real (R : ℝ) [Fact (0 ≤ (R:EReal))]
    (r : ℝ) (hr : 0 ≤ r) (hrR : r ≤ R) :
    closedPrefixProjection R (realTimeClamp r) = realTimeClamp r := by
  apply Subtype.ext
  change min (realTimeClamp (T := (⊤:EReal)) r : EReal) (R:EReal) =
    (realTimeClamp (T := (R:EReal)) r : EReal)
  rw [real_time_clamp_eq r hr le_top,real_time_clamp_eq r hr (EReal.coe_le_coe hrR)]
  exact min_eq_left (EReal.coe_le_coe hrR)

end Asakura.Chapter7

import FullAuditClosedHitting
import Chapter7ClockHalfTime

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2200000

/-- Include the infinite endpoint in the hitting set. Continuity is only
required at finite times, so no limit of a Brownian path at infinity is
implicitly assumed. -/
theorem open_hitting_set_closed
    {E : Type*} [TopologicalSpace E] (X : HalfClosedTime → E)
    (hc : ∀ t,t < ⊤ → ContinuousAt X t) (C : Set E) (hC : IsClosed C) :
    IsClosed {t | t = ⊤ ∨ X t ∈ C} := by
  rw [← isOpen_compl_iff,isOpen_iff_mem_nhds]
  intro t ht
  have hn : t ≠ ⊤ ∧ X t ∉ C := by simpa only [mem_compl_iff,mem_setOf_eq,not_or] using ht
  have hf := lt_top_iff_ne_top.mpr hn.1
  have he := (hc t hf).eventually (hC.isOpen_compl.mem_nhds hn.2)
  filter_upwards [he,eventually_lt_nhds hf] with s hs hsfin
  exact fun h => h.elim (fun heq => (ne_of_lt hsfin) heq) hs

theorem open_hitting_lower_event
    {E : Type*} [TopologicalSpace E] (X : HalfClosedTime → E)
    (hc : ∀ t,t < ⊤ → ContinuousAt X t) (C : Set E) (hC : IsClosed C)
    (t : HalfClosedTime) (ht : t < ⊤) :
    sInf {s | s = ⊤ ∨ X s ∈ C} ≤ t ↔ ∃ s ≤ t,X s ∈ C := by
  constructor
  · intro h
    have hmem := (open_hitting_set_closed X hc C hC).sInf_mem (show ({s : HalfClosedTime | s = ⊤ ∨ X s ∈ C}).Nonempty from ⟨⊤,Or.inl rfl⟩)
    exact ⟨_,h,hmem.resolve_left (ne_of_lt (lt_of_le_of_lt h ht))⟩
  · rintro ⟨s,hs,hmem⟩
    exact (sInf_le (show s ∈ {s : HalfClosedTime | s = ⊤ ∨ X s ∈ C} from Or.inr hmem)).trans hs

theorem open_continuous_hitting_stopping
    {Ω E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (F : HalfClosedTime → MeasurableSpace Ω) (hF : Monotone F)
    (X : HalfClosedTime → Ω → E)
    (hm : ∀ t,t < ⊤ → Measurable[F t] (X t))
    (hc : ∀ w t,t < ⊤ → ContinuousAt (fun s => X s w) t)
    (C : Set E) (hC : IsClosed C) :
    ∀ t,MeasurableSet[F t] {w | sInf {s | s = ⊤ ∨ X s w ∈ C} ≤ t} := by
  intro t
  letI : MeasurableSpace Ω := F t
  by_cases ht : t = ⊤
  · simp only [ht,le_top,setOf_true]
    exact MeasurableSet.univ
  have htf : t < ⊤ := lt_top_iff_ne_top.mpr ht
  by_cases hne : C.Nonempty
  swap
  · have he : C = ∅ := not_nonempty_iff_eq_empty.mp hne
    simp only [he,mem_empty_iff_false,or_false,setOf_eq_eq_singleton,sInf_singleton,top_le_iff]
    simp [ht]
  letI : Nonempty (Iic t) := ⟨⟨t,show t ≤ t from le_rfl⟩⟩
  letI : CompactSpace (Iic t) := isCompact_iff_compactSpace.mp (isClosed_Iic : IsClosed (Iic t)).isCompact
  let q := TopologicalSpace.denseSeq (Iic t)
  let d := fun w => ⨅ n,Metric.infDist (X (q n).val w) C
  have hd : Measurable d := Measurable.iInf fun n =>
    (Metric.continuous_infDist_pt C).measurable.comp
      ((hm _ (lt_of_le_of_lt (q n).property htf)).mono (hF (q n).property) le_rfl)
  have he : {w | sInf {s | s = ⊤ ∨ X s w ∈ C} ≤ t} = d ⁻¹' {0} := by
    ext w
    rw [mem_setOf_eq,open_hitting_lower_event _ (hc w) C hC t htf]
    change (∃ s ≤ t,X s w ∈ C) ↔ (⨅ n,Metric.infDist (X (q n).val w) C) = 0
    have hcont : Continuous (fun s : Iic t => X s.val w) := by
      apply continuous_iff_continuousAt.mpr
      intro s
      exact (hc w s.val (lt_of_le_of_lt s.property htf)).comp continuous_subtype_val.continuousAt
    rw [compact_dense_distance_zero q (TopologicalSpace.denseRange_denseSeq _) _ hcont C hC hne]
    constructor
    · rintro ⟨s,hs,h⟩; exact ⟨⟨s,hs⟩,h⟩
    · rintro ⟨s,h⟩; exact ⟨s.val,s.property,h⟩
  rw [he]
  exact hd (measurableSet_singleton 0)

end Asakura.Chapter7

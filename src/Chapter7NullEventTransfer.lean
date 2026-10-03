import FullAuditConditionalLimit

open MeasureTheory Set Filter
namespace Asakura.Chapter7

/-- Measurability of events survives a common null-set change when the
filtration contains the ambient measurable null sets. -/
theorem measurable_event_of_augmented_ae
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω)
    (G : MeasurableSpace Ω) (hG : G ≤ m)
    (hnull : ∀ N,MeasurableSet[m] N → P N = 0 → MeasurableSet[G] N)
    (A B : Set Ω) (ha : MeasurableSet[m] A) (hb : MeasurableSet[G] B)
    (he : ∀ᵐ w ∂P,w ∈ A ↔ w ∈ B) : MeasurableSet[G] A := by
  classical
  let N := (A \ B) ∪ (B \ A)
  have hNm : MeasurableSet[m] N := (ha.diff (hG B hb)).union ((hG B hb).diff ha)
  have hNz : P N = 0 := by
    apply measure_mono_null _ (ae_iff.mp he)
    intro w hw
    simp only [N,mem_union,mem_diff] at hw
    change ¬ (w ∈ A ↔ w ∈ B)
    rcases hw with h | h
    · exact fun he => h.2 (he.mp h.1)
    · exact fun he => h.2 (he.mpr h.1)
  have hNG := hnull N hNm hNz
  have hsmall : MeasurableSet[G] (A ∩ N) :=
    hnull _ (ha.inter hNm) (measure_mono_null inter_subset_right hNz)
  have hset : A = (B \ N) ∪ (A ∩ N) := by
    ext w
    simp only [N,mem_union,mem_diff,mem_inter_iff]
    tauto
  rw [hset]
  exact (hb.diff hNG).union hsmall

end Asakura.Chapter7

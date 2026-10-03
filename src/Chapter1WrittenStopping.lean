import Chapter1WrittenSteps
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Instances.EReal.Lemmas

/- The ambient sigma algebra and the dense set plus gap endpoints are exactly
those in the manuscript. There is no WithTop representation of stopping times. -/
open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter1Written

/-- prop:st1, with complements and countable unions checked directly. -/
@[instance_reducible] def writtenStoppedSpace {Ω ι : Type*} (m : MeasurableSpace Ω)
    [LinearOrder ι] (F : ι → MeasurableSpace Ω) (τ : Ω → ι)
    (hτ : ∀ i, MeasurableSet[F i] {ω | τ ω ≤ i}) : MeasurableSpace Ω where
  MeasurableSet' A := MeasurableSet[m] A ∧ ∀ i, MeasurableSet[F i] (A ∩ {ω | τ ω ≤ i})
  measurableSet_empty := by simp
  measurableSet_compl A hA := by
    refine ⟨hA.1.compl, fun i => ?_⟩
    have he : Aᶜ ∩ {ω | τ ω ≤ i} = {ω | τ ω ≤ i} \ (A ∩ {ω | τ ω ≤ i}) := by
      ext ω; simp; tauto
    rw [he]
    exact (hτ i).diff (hA.2 i)
  measurableSet_iUnion A hA := by
    refine ⟨MeasurableSet.iUnion (fun n => (hA n).1), fun i => ?_⟩
    rw [Set.iUnion_inter]
    exact MeasurableSet.iUnion (fun n => (hA n).2 i)

/-- The literal stopping-time min/max event equalities. -/
theorem written_stopping_min_max {Ω ι : Type*} [LinearOrder ι]
    (F : ι → MeasurableSpace Ω) (τ σ : Ω → ι)
    (hτ : ∀ i, MeasurableSet[F i] {ω | τ ω ≤ i})
    (hσ : ∀ i, MeasurableSet[F i] {ω | σ ω ≤ i}) :
    (∀ i, MeasurableSet[F i] {ω | min (τ ω) (σ ω) ≤ i}) ∧
    (∀ i, MeasurableSet[F i] {ω | max (τ ω) (σ ω) ≤ i}) := by
  constructor
  · intro i
    simpa only [min_le_iff, ofPred_or] using (hτ i).union (hσ i)
  · intro i
    simpa only [max_le_iff, ofPred_and] using (hτ i).inter (hσ i)

/-- prop:st2: equality of the stopped sigma algebra and the intersection. -/
theorem written_stopped_min_sigma {Ω ι : Type*} (m : MeasurableSpace Ω) [LinearOrder ι]
    (F : ι → MeasurableSpace Ω) (τ σ : Ω → ι)
    (hτ : ∀ i, MeasurableSet[F i] {ω | τ ω ≤ i})
    (hσ : ∀ i, MeasurableSet[F i] {ω | σ ω ≤ i}) :
    writtenStoppedSpace m F (fun ω => min (τ ω) (σ ω)) (written_stopping_min_max F τ σ hτ hσ).1 =
      writtenStoppedSpace m F τ hτ ⊓ writtenStoppedSpace m F σ hσ := by
  ext A
  change (MeasurableSet[m] A ∧ ∀ i, MeasurableSet[F i] (A ∩ {ω | min (τ ω) (σ ω) ≤ i})) ↔
    (MeasurableSet[m] A ∧ ∀ i, MeasurableSet[F i] (A ∩ {ω | τ ω ≤ i})) ∧
    (MeasurableSet[m] A ∧ ∀ i, MeasurableSet[F i] (A ∩ {ω | σ ω ≤ i}))
  constructor
  · intro h
    constructor
    · refine ⟨h.1, fun i => ?_⟩
      have he : A ∩ {ω | τ ω ≤ i} = (A ∩ {ω | min (τ ω) (σ ω) ≤ i}) ∩ {ω | τ ω ≤ i} := by
        ext ω; simp only [mem_inter_iff, mem_ofPred_eq, min_le_iff]; tauto
      rw [he]
      exact (h.2 i).inter (hτ i)
    · refine ⟨h.1, fun i => ?_⟩
      have he : A ∩ {ω | σ ω ≤ i} = (A ∩ {ω | min (τ ω) (σ ω) ≤ i}) ∩ {ω | σ ω ≤ i} := by
        ext ω; simp only [mem_inter_iff, mem_ofPred_eq, min_le_iff]; tauto
      rw [he]
      exact (h.2 i).inter (hσ i)
  · rintro ⟨hA, hB⟩
    refine ⟨hA.1, fun i => ?_⟩
    simpa only [min_le_iff, ofPred_or, inter_union_distrib_left] using (hA.2 i).union (hB.2 i)

/-- The manuscript's countable set: dense points together with left endpoints
of adjacent pairs. The subtype topology may be finer than its order topology. -/
theorem extended_real_countable_separator (Λ : Set EReal) :
    ∃ D : Set Λ, D.Countable ∧ ∀ a b : Λ, a < b → ∃ q ∈ D, a ≤ q ∧ q < b := by
  classical
  obtain ⟨D, hD, hdense⟩ := TopologicalSpace.exists_countable_dense Λ
  let L : Set Λ := {a | ∃ b, a < b ∧ ∀ c, a < c → b ≤ c}
  have hL : L.Countable := by
    apply (countable_image_lt_image_Ioi (fun a : Λ => (a : EReal))).mono
    rintro a ⟨b, hab, hnext⟩
    exact ⟨(b : EReal), hab, fun c hc => hnext c hc⟩
  refine ⟨D ∪ L, hD.union hL, ?_⟩
  intro a b hab
  by_cases hmid : ∃ c : Λ, a < c ∧ c < b
  · have hopen : IsOpen (Ioo a b : Set Λ) :=
      continuous_subtype_val.isOpen_preimage _ isOpen_Ioo
    obtain ⟨q, hq, hqab⟩ := hdense.exists_mem_open hopen hmid
    exact ⟨q, Or.inl hq, hqab.1.le, hqab.2⟩
  · refine ⟨a, Or.inr ?_, le_rfl, hab⟩
    refine ⟨b, hab, ?_⟩
    intro c hac
    by_contra hbc
    exact hmid ⟨c, hac, lt_of_not_ge hbc⟩

/-- The exact countable-union identity for the strict comparison event. -/
theorem written_comparison_event_identity {Ω ι : Type*} [LinearOrder ι]
    (D : Set ι) (hsep : ∀ a b, a < b → ∃ q ∈ D, a ≤ q ∧ q < b)
    (τ σ : Ω → ι) (i : ι) :
    {ω | τ ω < σ ω} ∩ {ω | min (τ ω) (σ ω) ≤ i} =
      {ω | i < σ ω ∧ τ ω ≤ i} ∪
      ⋃ q ∈ D, ⋃ (_ : q < i), {ω | τ ω ≤ q ∧ q < σ ω ∧ σ ω ≤ i} := by
  ext ω
  simp only [mem_inter_iff, mem_ofPred_eq, min_le_iff, mem_union, mem_iUnion]
  constructor
  · rintro ⟨h, hm⟩
    have ht : τ ω ≤ i := hm.elim id (fun hs => h.le.trans hs)
    by_cases hs : i < σ ω
    · exact Or.inl ⟨hs, ht⟩
    · obtain ⟨q, hq, htq, hqs⟩ := hsep _ _ h
      exact Or.inr ⟨q, hq, hqs.trans_le (le_of_not_gt hs), htq, hqs, le_of_not_gt hs⟩
  · rintro (⟨hs, ht⟩ | ⟨q, hq, hqi, htq, hqs, hsi⟩)
    · exact ⟨ht.trans_lt hs, Or.inl ht⟩
    · exact ⟨htq.trans_lt hqs, Or.inr hsi⟩

/-- Countability makes the displayed union measurable at every deterministic time. -/
theorem written_strict_comparison_measurable {Ω ι : Type*} (m : MeasurableSpace Ω)
    [LinearOrder ι] (F : ι → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ i, F i ≤ m)
    (D : Set ι) (hD : D.Countable)
    (hsep : ∀ a b, a < b → ∃ q ∈ D, a ≤ q ∧ q < b)
    (τ σ : Ω → ι) (hτ : ∀ i, MeasurableSet[F i] {ω | τ ω ≤ i})
    (hσ : ∀ i, MeasurableSet[F i] {ω | σ ω ≤ i}) :
    MeasurableSet[writtenStoppedSpace m F τ hτ ⊓ writtenStoppedSpace m F σ hσ]
      {ω | τ ω < σ ω} := by
  rw [← written_stopped_min_sigma]
  change MeasurableSet[m] {ω | τ ω < σ ω} ∧ _
  constructor
  · have he : {ω | τ ω < σ ω} = ⋃ q ∈ D, {ω | τ ω ≤ q} ∩ {ω | q < σ ω} := by
      ext ω
      simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff]
      constructor
      · intro hh
        obtain ⟨q, hq, htq, hqs⟩ := hsep _ _ hh
        exact ⟨q, hq, htq, hqs⟩
      · rintro ⟨q, hq, h1, h2⟩; exact h1.trans_lt h2
    rw [he]
    apply MeasurableSet.biUnion hD
    intro q hq
    exact (hle q _ (hτ q)).inter (by simpa only [compl_ofPred, not_le] using (hle q _ (hσ q)).compl)
  · intro i
    rw [written_comparison_event_identity D hsep]
    apply MeasurableSet.union
    · simpa only [ofPred_and, compl_ofPred, not_le] using (hσ i).compl.inter (hτ i)
    · apply MeasurableSet.biUnion hD
      intro q hq
      apply MeasurableSet.iUnion
      intro hqi
      have hs : MeasurableSet[F i] {ω | q < σ ω} := by
        simpa only [compl_ofPred, not_le] using (hF hqi.le _ (hσ q)).compl
      simpa only [ofPred_and, inter_assoc] using ((hF hqi.le _ (hτ q)).inter hs).inter (hσ i)

/-- Both comparison events, for the manuscript's arbitrary subset of extended reals. -/
theorem written_extended_comparison {Ω : Type*} (m : MeasurableSpace Ω) (Λ : Set EReal)
    (F : Λ → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ i, F i ≤ m)
    (τ σ : Ω → Λ) (hτ : ∀ i, MeasurableSet[F i] {ω | τ ω ≤ i})
    (hσ : ∀ i, MeasurableSet[F i] {ω | σ ω ≤ i}) :
    MeasurableSet[writtenStoppedSpace m F τ hτ ⊓ writtenStoppedSpace m F σ hσ] {ω | τ ω < σ ω} ∧
    MeasurableSet[writtenStoppedSpace m F τ hτ ⊓ writtenStoppedSpace m F σ hσ] {ω | τ ω ≤ σ ω} := by
  obtain ⟨D, hD, hsep⟩ := extended_real_countable_separator Λ
  refine ⟨written_strict_comparison_measurable m F hF hle D hD hsep τ σ hτ hσ, ?_⟩
  have h := (written_strict_comparison_measurable m F hF hle D hD hsep σ τ hσ hτ).compl
  rw [inf_comm] at h
  simpa only [compl_ofPred, not_lt] using h

end Asakura.Chapter1Written

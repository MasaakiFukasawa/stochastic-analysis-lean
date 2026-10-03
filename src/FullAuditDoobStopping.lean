import FullAuditOptionalSampling
import Mathlib.Data.Finset.Max

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.FullAudit
open Asakura.Chapter1Written

noncomputable def cappedFirstHit {Ω ι : Type*} [Fintype ι] [LinearOrder ι] [OrderTop ι]
    (X : ι → Ω → ℝ) (a : ℝ) (ω : Ω) : ι := by
  classical
  exact (Finset.univ.filter (fun i => a ≤ X i ω ∨ i = ⊤)).min'
    ⟨⊤,by simp⟩

/-- The event description proves the first hit capped at the final time is a stopping time. -/
theorem cappedFirstHit_le_iff {Ω ι : Type*} [Fintype ι] [LinearOrder ι] [OrderTop ι]
    (X : ι → Ω → ℝ) (a : ℝ) (ω : Ω) (k : ι) :
    cappedFirstHit X a ω ≤ k ↔ ∃ j, j ≤ k ∧ (a ≤ X j ω ∨ j = ⊤) := by
  classical
  let S := Finset.univ.filter (fun i => a ≤ X i ω ∨ i = ⊤)
  have hs : S.Nonempty := ⟨⊤,by simp [S]⟩
  change S.min' hs ≤ k ↔ _
  constructor
  · intro h
    exact ⟨S.min' hs,h,(Finset.mem_filter.mp (S.min'_mem hs)).2⟩
  · rintro ⟨j,hjk,hj⟩
    exact (S.min'_le j (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩)).trans hjk

theorem cappedFirstHit_stopping {Ω ι : Type*} [Fintype ι] [LinearOrder ι] [OrderTop ι]
    (F : ι → MeasurableSpace Ω) (hF : Monotone F) (X : ι → Ω → ℝ)
    (hX : ∀ i, Measurable[F i] (X i)) (a : ℝ) (k : ι) :
    MeasurableSet[F k] {ω | cappedFirstHit X a ω ≤ k} := by
  have he : {ω | cappedFirstHit X a ω ≤ k} =
      ⋃ j : Iic k, {ω | a ≤ X j.val ω ∨ j.val = ⊤} := by
    ext ω
    simp only [mem_ofPred_eq,cappedFirstHit_le_iff,mem_iUnion]
    constructor
    · rintro ⟨j,hj,h⟩; exact ⟨⟨j,hj⟩,h⟩
    · rintro ⟨j,h⟩; exact ⟨j.val,j.property,h⟩
  rw [he]
  apply MeasurableSet.iUnion
  intro j
  by_cases hj : j.val = ⊤
  · simp [hj]
  · simp only [hj,or_false]
    exact measurableSet_le measurable_const ((hX j.val).mono (hF j.property) le_rfl)

theorem cappedFirstHit_no_hit {Ω ι : Type*} [Fintype ι] [LinearOrder ι] [OrderTop ι]
    (X : ι → Ω → ℝ) (a : ℝ) (ω : Ω) (h : ¬ ∃ i, a ≤ X i ω) :
    cappedFirstHit X a ω = ⊤ := by
  classical
  have hm := (Finset.univ.filter (fun i => a ≤ X i ω ∨ i = ⊤)).min'_mem
    (show (Finset.univ.filter (fun i => a ≤ X i ω ∨ i = ⊤)).Nonempty from ⟨⊤,by simp⟩)
  have hp : a ≤ X (cappedFirstHit X a ω) ω ∨ cappedFirstHit X a ω = ⊤ :=
    (Finset.mem_filter.mp hm).2
  exact hp.resolve_left (fun hi => h ⟨_,hi⟩)

theorem cappedFirstHit_level {Ω ι : Type*} [Fintype ι] [LinearOrder ι] [OrderTop ι]
    (X : ι → Ω → ℝ) (a : ℝ) (ω : Ω) (h : ∃ i, a ≤ X i ω) :
    a ≤ X (cappedFirstHit X a ω) ω := by
  classical
  have hm := (Finset.univ.filter (fun i => a ≤ X i ω ∨ i = ⊤)).min'_mem
    (show (Finset.univ.filter (fun i => a ≤ X i ω ∨ i = ⊤)).Nonempty from ⟨⊤,by simp⟩)
  have hp : a ≤ X (cappedFirstHit X a ω) ω ∨ cappedFirstHit X a ω = ⊤ :=
    (Finset.mem_filter.mp hm).2
  rcases hp with hp | ht
  · exact hp
  · obtain ⟨j,hj⟩ := h
    have hle := (cappedFirstHit_le_iff X a ω j).mpr ⟨j,le_rfl,Or.inl hj⟩
    rw [ht] at hle
    have hjtop : j = ⊤ := top_le_iff.mp hle
    simpa [ht,hjtop] using hj

end Asakura.FullAudit

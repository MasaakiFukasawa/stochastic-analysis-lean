import Chapter1WrittenStopping

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.FullAudit
open Asakura.Chapter1Written
attribute [local instance] Classical.propDecidable

/-- The event formula in the two-valued stopping-time example. -/
theorem two_time_event {Ω ι : Type*} [LinearOrder ι] (A : Set Ω)
    (a b i : ι) (hab : a ≤ b) :
    {ω | (if ω ∈ A then a else b) ≤ i} =
      if b ≤ i then univ else if a ≤ i then A else ∅ := by
  classical
  ext ω
  by_cases hb : b ≤ i
  · by_cases hA : ω ∈ A <;> simp [hb,hab.trans hb,hA]
  · by_cases ha : a ≤ i
    · by_cases hA : ω ∈ A <;> simp [hb,ha,hA]
    · by_cases hA : ω ∈ A <;> simp [hb,ha,hA]

/-- Adaptedness of the two-valued stopping time, including a=b. -/
theorem two_time_stopping {Ω ι : Type*} [LinearOrder ι]
    (F : ι → MeasurableSpace Ω) (hF : Monotone F)
    (A : Set Ω) (a b : ι) (hab : a ≤ b) (hA : MeasurableSet[F a] A) :
    ∀ i, MeasurableSet[F i] {ω | (if ω ∈ A then a else b) ≤ i} := by
  classical
  intro i
  rw [two_time_event A a b i hab]
  split_ifs with hb ha
  · exact MeasurableSet.univ
  · exact hF ha _ hA
  · exact @MeasurableSet.empty Ω (F i)

/-- Exercise on the sigma algebra at a two-valued stopping time. -/
theorem two_time_stopped_sigma {Ω ι : Type*} (m : MeasurableSpace Ω) [LinearOrder ι]
    (F : ι → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ i, F i ≤ m)
    (A : Set Ω) (a b : ι) (hab : a ≤ b) (hA : MeasurableSet[F a] A)
    (B : Set Ω) :
    MeasurableSet[writtenStoppedSpace m F (fun ω => if ω ∈ A then a else b)
      (two_time_stopping F hF A a b hab hA)] B ↔
      MeasurableSet[F b] B ∧ MeasurableSet[F a] (A ∩ B) := by
  classical
  constructor
  · intro h
    have hb := h.2 b
    have ha := h.2 a
    rw [two_time_event A a b b hab] at hb
    simp only [le_refl,ite_true,inter_univ] at hb
    refine ⟨hb,?_⟩
    by_cases hba : b ≤ a
    · exact hA.inter (hF hba _ hb)
    · rw [two_time_event A a b a hab] at ha
      simpa [hba,inter_comm] using ha
  · rintro ⟨hb,ha⟩
    refine ⟨hle b _ hb,fun i => ?_⟩
    rw [two_time_event A a b i hab]
    split_ifs with hbi hai
    · simpa using hF hbi _ hb
    · simpa only [inter_comm] using hF hai _ ha
    · simp

/-- Every subset of a second-countable ordered space has a countable cofinal
subset. A greatest point is kept explicitly, so no endpoint is lost. -/
theorem countable_cofinal_subset {ι : Type*} [LinearOrder ι] [TopologicalSpace ι]
    [OrderClosedTopology ι] [SecondCountableTopology ι] (S : Set ι) :
    ∃ D : Set ι, D.Countable ∧ D ⊆ S ∧ ∀ x ∈ S, ∃ y ∈ D, x ≤ y := by
  classical
  by_cases hg : ∃ y ∈ S, ∀ x ∈ S, x ≤ y
  · obtain ⟨y,hy,hmax⟩ := hg
    exact ⟨{y},countable_singleton y,singleton_subset_iff.mpr hy,
      fun x hx => ⟨y,mem_singleton y,hmax x hx⟩⟩
  · obtain ⟨D,hD,hd⟩ := TopologicalSpace.exists_countable_dense S
    refine ⟨Subtype.val '' D,hD.image _,by rintro x ⟨y,hy,rfl⟩; exact y.property,?_⟩
    intro x hx
    have hnext : ∃ y ∈ S, x < y := by
      by_contra hn
      apply hg
      exact ⟨x,hx,fun y hy => le_of_not_gt (fun h => hn ⟨y,hy,h⟩)⟩
    obtain ⟨y,hy,hxy⟩ := hnext
    have hop : IsOpen {z : S | x < (z:ι)} := continuous_subtype_val.isOpen_preimage _ isOpen_Ioi
    obtain ⟨z,hz,hxz⟩ := hd.exists_mem_open hop ⟨⟨y,hy⟩,hxy⟩
    exact ⟨z,mem_image_of_mem _ hz,hxz.le⟩

/-- Monotone delay of a stopping time. Left continuity, as assumed in the
exercise, is unnecessary: the countable cofinal set handles either endpoint. -/
theorem monotone_delay_stopping {Ω ι : Type*} [LinearOrder ι] [TopologicalSpace ι]
    [OrderClosedTopology ι] [SecondCountableTopology ι]
    (F : ι → MeasurableSpace Ω) (hF : Monotone F) (τ : Ω → ι)
    (hτ : ∀ i, MeasurableSet[F i] {ω | τ ω ≤ i}) (g : ι → ι)
    (hg : Monotone g) (hdelay : ∀ i, i ≤ g i) :
    ∀ i, MeasurableSet[F i] {ω | g (τ ω) ≤ i} := by
  intro i
  obtain ⟨D,hD,hDS,hcof⟩ := countable_cofinal_subset {j | g j ≤ i}
  have he : {ω | g (τ ω) ≤ i} = ⋃ j ∈ D, {ω | τ ω ≤ j} := by
    ext ω
    simp only [mem_setOf_eq,mem_iUnion]
    constructor
    · intro h
      obtain ⟨j,hj,htj⟩ := hcof (τ ω) h
      exact ⟨j,hj,htj⟩
    · rintro ⟨j,hj,htj⟩
      exact (hg htj).trans (hDS hj)
  rw [he]
  exact MeasurableSet.biUnion hD (fun j hj => hF ((hdelay j).trans (hDS hj)) _ (hτ j))

end Asakura.FullAudit

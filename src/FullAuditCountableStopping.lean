import Chapter1WrittenStoppedMeasurable
import Chapter1WrittenJensen

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.FullAudit
open Asakura.Chapter1Written

/-- Countable time fibers are measurable at their own time. -/
theorem countable_stopping_fiber {Ω ι : Type*} [LinearOrder ι] [Countable ι]
    (F : ι → MeasurableSpace Ω) (hF : Monotone F) (τ : Ω → ι)
    (hτ : ∀ i, MeasurableSet[F i] {ω | τ ω ≤ i}) (i : ι) :
    MeasurableSet[F i] {ω | τ ω = i} := by
  have he : {ω | τ ω = i} = {ω | τ ω ≤ i} \ ⋃ j : Iio i, {ω | τ ω ≤ j.val} := by
    ext ω
    simp only [mem_ofPred_eq, Set.mem_sdiff, mem_iUnion, not_exists]
    constructor
    · intro h; subst h
      exact ⟨le_rfl, fun j hj => (not_le_of_gt j.property) hj⟩
    · rintro ⟨hle,h⟩
      exact le_antisymm hle (le_of_not_gt (fun hlt => h ⟨τ ω,hlt⟩ le_rfl))
  rw [he]
  exact (hτ i).diff (MeasurableSet.iUnion fun j => hF j.property.le _ (hτ j.val))

/-- Intersecting a stopped measurable event with a time fiber is measurable at that time. -/
theorem stopped_event_fiber {Ω ι : Type*} (m : MeasurableSpace Ω)
    [LinearOrder ι] [Countable ι] (F : ι → MeasurableSpace Ω) (hF : Monotone F)
    (τ : Ω → ι) (hτ : ∀ i, MeasurableSet[F i] {ω | τ ω ≤ i})
    {A : Set Ω} (hA : MeasurableSet[writtenStoppedSpace m F τ hτ] A) (i : ι) :
    MeasurableSet[F i] (A ∩ {ω | τ ω = i}) := by
  have he : A ∩ {ω | τ ω = i} = (A ∩ {ω | τ ω ≤ i}) \
      ⋃ j : Iio i, (A ∩ {ω | τ ω ≤ j.val}) := by
    ext ω
    simp only [mem_inter_iff, mem_ofPred_eq, Set.mem_sdiff, mem_iUnion, not_exists]
    constructor
    · rintro ⟨ha,hi⟩
      exact ⟨⟨ha,hi.le⟩,fun j hj => (not_le_of_gt j.property) (hi ▸ hj.2)⟩
    · rintro ⟨⟨ha,hle⟩,h⟩
      exact ⟨ha,le_antisymm hle (le_of_not_gt (fun hlt => h ⟨τ ω,hlt⟩ ⟨ha,le_rfl⟩))⟩
  rw [he]
  exact (hA.2 i).diff (MeasurableSet.iUnion fun j => hF j.property.le _ (hA.2 j.val))

/-- The fiber criterion for the manuscript's stopped sigma algebra. -/
theorem stopped_measurable_of_fibers {Ω ι : Type*} (m : MeasurableSpace Ω)
    [LinearOrder ι] [Countable ι] (F : ι → MeasurableSpace Ω) (hF : Monotone F)
    (hle : ∀ i, F i ≤ m) (τ : Ω → ι) (hτ : ∀ i, MeasurableSet[F i] {ω | τ ω ≤ i})
    {A : Set Ω} (hA : ∀ i, MeasurableSet[F i] (A ∩ {ω | τ ω = i})) :
    MeasurableSet[writtenStoppedSpace m F τ hτ] A := by
  have hUnion : A = ⋃ i, A ∩ {ω | τ ω = i} := by ext ω; simp
  constructor
  · rw [hUnion]
    exact MeasurableSet.iUnion fun i => hle i _ (hA i)
  · intro k
    have he : A ∩ {ω | τ ω ≤ k} = ⋃ i : Iic k, A ∩ {ω | τ ω = i.val} := by
      ext ω
      simp only [mem_inter_iff, mem_ofPred_eq, mem_iUnion]
      constructor
      · rintro ⟨ha,hk⟩; exact ⟨⟨τ ω,hk⟩,ha,rfl⟩
      · rintro ⟨i,ha,hi⟩; exact ⟨ha,hi ▸ i.property⟩
    rw [he]
    exact MeasurableSet.iUnion fun i => hF i.property _ (hA i.val)

/-- A countable adapted process evaluated at the stopping time is measurable
for the stopped sigma algebra, by the disjoint time fibers. -/
theorem stopped_value_measurable_countable {Ω ι : Type*} (m : MeasurableSpace Ω)
    [LinearOrder ι] [Countable ι] (F : ι → MeasurableSpace Ω) (hF : Monotone F)
    (hle : ∀ i, F i ≤ m) (τ : Ω → ι) (hτ : ∀ i, MeasurableSet[F i] {ω | τ ω ≤ i})
    (X : ι → Ω → ℝ) (hX : ∀ i, Measurable[F i] (X i)) :
    Measurable[writtenStoppedSpace m F τ hτ] (fun ω => X (τ ω) ω) := by
  intro B hB
  apply stopped_measurable_of_fibers m F hF hle τ hτ
  intro i
  have he : (fun ω => X (τ ω) ω) ⁻¹' B ∩ {ω | τ ω = i} = (X i) ⁻¹' B ∩ {ω | τ ω = i} := by
    ext ω; simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq]
    constructor <;> rintro ⟨h,hτi⟩ <;> simpa [hτi] using And.intro h hτi
  rw [he]
  exact (hX i hB).inter (countable_stopping_fiber F hF τ hτ i)

end Asakura.FullAudit

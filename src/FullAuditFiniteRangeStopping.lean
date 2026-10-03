import FullAuditOptionalSampling
import Chapter2WrittenGridStopping

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.FullAudit
open Asakura.Chapter1Written Asakura.Chapter2Written

/-- Restricting time to a countable set containing every value of the stopping
 time does not change the manuscript's stopped sigma algebra. -/
theorem stopped_space_countable_range {Ω ι : Type*} (m : MeasurableSpace Ω)
    [LinearOrder ι] (F : ι → MeasurableSpace Ω) (hF : Monotone F)
    (τ : Ω → ι) (hτ : ∀ i, MeasurableSet[F i] {ω | τ ω ≤ i})
    (D : Set ι) (hD : D.Countable) (hr : ∀ ω, τ ω ∈ D) :
    writtenStoppedSpace m (fun i : D => F i) (fun ω => ⟨τ ω,hr ω⟩)
      (fun i => hτ i) = writtenStoppedSpace m F τ hτ := by
  apply le_antisymm
  · intro A hA
    refine ⟨hA.1,fun t => ?_⟩
    have he : A ∩ {ω | τ ω ≤ t} = ⋃ q ∈ D, ⋃ (_ : q ≤ t), A ∩ {ω | τ ω ≤ q} := by
      ext ω
      simp only [mem_inter_iff,mem_ofPred_eq,mem_iUnion]
      constructor
      · rintro ⟨ha,ht⟩; exact ⟨τ ω,hr ω,ht,ha,le_rfl⟩
      · rintro ⟨q,hq,hqt,ha,hω⟩; exact ⟨ha,hω.trans hqt⟩
    rw [he]
    apply MeasurableSet.biUnion hD
    intro q hq
    apply MeasurableSet.iUnion
    intro hqt
    exact hF hqt _ (hA.2 ⟨q,hq⟩)
  · intro A hA
    exact ⟨hA.1,fun i => hA.2 i⟩

/-- The countable-time result is applied to the actual range of a grid time. -/
theorem optional_sampling_countable_range {Ω ι : Type*} {m : MeasurableSpace Ω}
    [LinearOrder ι] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : ι → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ i, F i ≤ m)
    (τ : Ω → ι) (hτ : ∀ i, MeasurableSet[F i] {ω | τ ω ≤ i})
    (hcount : (range τ).Countable) {Y : Ω → ℝ} (hY : Integrable Y P)
    (X : ι → Ω → ℝ) (hX : ∀ i, X i =ᵐ[P] P[Y | F i]) :
    (fun ω => X (τ ω) ω) =ᵐ[P] P[Y | writtenStoppedSpace m F τ hτ] := by
  letI : Countable (range τ) := hcount.to_subtype
  have h := optional_sampling_arbitrary_versions P (fun i : range τ => F i)
    (fun _ _ hij => hF hij) (fun i => hle i)
    (fun ω => ⟨τ ω,mem_range_self ω⟩) (fun i => hτ i) hY
    (fun i => X i) (fun i => hX i)
  rw [stopped_space_countable_range m F hF τ hτ (range τ) hcount (fun ω => mem_range_self ω)] at h
  exact h

end Asakura.FullAudit

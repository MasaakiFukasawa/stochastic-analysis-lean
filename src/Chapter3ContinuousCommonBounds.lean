import Chapter2CommonTimeEquality

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter3Complete

/-- Deterministic-time order bounds between continuous processes hold
simultaneously on the entire separable time domain. -/
theorem continuous_process_common_bounds
    {Ω D : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [TopologicalSpace D] [TopologicalSpace.SeparableSpace D] [Nonempty D]
    (X Y : D → Ω → ℝ) (hX : ∀ ω, Continuous (fun t => X t ω))
    (hY : ∀ ω, Continuous (fun t => Y t ω))
    (hb : ∀ t, ∀ᵐ ω ∂P, 0 ≤ X t ω ∧ X t ω ≤ Y t ω) :
    ∀ᵐ ω ∂P, ∀ t, 0 ≤ X t ω ∧ X t ω ≤ Y t ω := by
  let q := TopologicalSpace.denseSeq D
  filter_upwards [ae_all_iff.mpr (fun n => hb (q n))] with ω hω
  have hc : IsClosed {t | 0 ≤ X t ω ∧ X t ω ≤ Y t ω} :=
    (isClosed_le continuous_const (hX ω)).inter (isClosed_le (hX ω) (hY ω))
  have hs : range q ⊆ {t | 0 ≤ X t ω ∧ X t ω ≤ Y t ω} := by
    rintro t ⟨n,rfl⟩
    exact hω n
  have hu : univ ⊆ {t | 0 ≤ X t ω ∧ X t ω ≤ Y t ω} := by
    rw [← (TopologicalSpace.denseRange_denseSeq D).closure_range]
    exact hc.closure_subset_iff.mpr hs
  exact fun t => hu (mem_univ t)

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.continuous_process_common_bounds

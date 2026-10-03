import Chapter2PathMetricSubsequence

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

theorem path_distance_self {D : Type*} [TopologicalSpace D]
    (K : CompactExhaustion D) (f : C(D,ℝ)) : pathDistance K f f = 0 := by
  simp [pathDistance,compactStageDist]

theorem path_distance_symm {D : Type*} [TopologicalSpace D]
    (K : CompactExhaustion D) (f g : C(D,ℝ)) : pathDistance K f g = pathDistance K g f := by
  simp only [pathDistance,compactStageDist,dist_comm]

theorem path_distance_eq_zero_iff {D : Type*} [TopologicalSpace D]
    (K : CompactExhaustion D) (f g : C(D,ℝ)) : pathDistance K f g = 0 ↔ f = g := by
  constructor
  · intro hz
    letI (n : ℕ) : CompactSpace (K n) := isCompact_iff_compactSpace.1 (K.isCompact n)
    have hstage (n) : compactStageDist K n f g = 0 := by
      have h := path_distance_controls_stage K f g n
      rw [hz] at h
      by_contra hne
      have hp := lt_of_le_of_ne (compact_stage_distance_nonneg K n f g) (Ne.symm hne)
      have hw : 0 < (1/2:ℝ)^(n+1) := pow_pos (by norm_num) _
      exact not_lt_of_ge h (mul_pos hw (lt_min zero_lt_one hp))
    apply ContinuousMap.ext
    intro x
    obtain ⟨n,hxn⟩ := K.exists_mem x
    have h := ContinuousMap.dist_apply_le_dist (f := f.restrict (K n)) (g := g.restrict (K n)) ⟨x,hxn⟩
    change dist (f x) (g x) ≤ compactStageDist K n f g at h
    rw [hstage n] at h
    exact dist_eq_zero.1 (le_antisymm h dist_nonneg)
  · rintro rfl
    exact path_distance_self K f

/-- The expectation distance is zero exactly for indistinguishable
continuous paths, justifying the quotient used in the manuscript. -/
theorem expected_path_distance_zero_iff
    {Ω D : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    [TopologicalSpace D] [T2Space D] [LocallyCompactSpace D] [SecondCountableTopology D]
    (K : CompactExhaustion D) (X Y : Ω → C(D,ℝ)) (hX : Measurable X) (hY : Measurable Y) :
    (∫ ω, pathDistance K (X ω) (Y ω) ∂P) = 0 ↔ X =ᵐ[P] Y := by
  rw [integral_eq_zero_iff_of_nonneg_ae (.of_forall fun ω => (path_distance_bounds K _ _).1)
    (integrable_path_distance P K X Y hX hY)]
  constructor
  · intro h
    exact h.mono fun ω hω => (path_distance_eq_zero_iff K _ _).1 hω
  · intro h
    exact h.mono fun ω hω => (path_distance_eq_zero_iff K _ _).2 hω

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.path_distance_self
#print axioms Asakura.Chapter2Complete.path_distance_symm
#print axioms Asakura.Chapter2Complete.path_distance_eq_zero_iff
#print axioms Asakura.Chapter2Complete.expected_path_distance_zero_iff

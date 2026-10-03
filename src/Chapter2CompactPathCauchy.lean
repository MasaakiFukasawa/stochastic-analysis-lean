import Chapter2RandomCauchy
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.UniformSpace.CompactConvergence

open MeasureTheory Set Filter
open scoped Topology ENNReal Uniformity
namespace Asakura.Chapter2Complete
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

noncomputable def compactStageDist {D : Type*} [TopologicalSpace D]
    (K : CompactExhaustion D) (n : ℕ) (f g : C(D,ℝ)) : ℝ := by
  letI : CompactSpace (K n) := isCompact_iff_compactSpace.1 (K.isCompact n)
  exact dist (f.restrict (K n)) (g.restrict (K n))

theorem compact_stage_distance_mono {D : Type*} [TopologicalSpace D]
    (K : CompactExhaustion D) (f g : C(D,ℝ)) {i j : ℕ} (hij : i ≤ j) :
    compactStageDist K i f g ≤ compactStageDist K j f g := by
  letI (n : ℕ) : CompactSpace (K n) := isCompact_iff_compactSpace.1 (K.isCompact n)
  apply (ContinuousMap.dist_le dist_nonneg).2
  intro x
  exact ContinuousMap.dist_apply_le_dist (f := f.restrict (K j)) (g := g.restrict (K j))
    ⟨x.val,K.subset hij x.property⟩

/-- Compact exhaustion gives a countable criterion for Cauchy convergence
in the local uniform topology of continuous paths. -/
theorem compact_stage_cauchy {D : Type*} [TopologicalSpace D]
    (K : CompactExhaustion D) (X : ℕ → C(D,ℝ))
    (h : ∀ j ε, 0 < ε → ∃ N, ∀ m ≥ N, ∀ n ≥ N, compactStageDist K j (X m) (X n) < ε) :
    CauchySeq X := by
  letI (n : ℕ) : CompactSpace (K n) := isCompact_iff_compactSpace.1 (K.isCompact n)
  apply (K.hasBasis_compactConvergenceUniformity Metric.uniformity_basis_dist).cauchySeq_iff.2
  rintro ⟨j,ε⟩ hε
  obtain ⟨N,hN⟩ := h j ε hε
  refine ⟨N,fun m hm n hn x hx => ?_⟩
  exact (ContinuousMap.dist_apply_le_dist (f := (X m).restrict (K j))
    (g := (X n).restrict (K j)) ⟨x,hx⟩).trans_lt (hN m hm n hn)

/-- Diagonal increment control on expanding compact intervals gives an
almost-sure locally uniform limit. This constructs a continuous limit path,
not merely separate pointwise limits. -/
theorem diagonal_compact_increment_limit
    {Ω D : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [TopologicalSpace D] [LocallyCompactSpace D] [T2Space D]
    (K : CompactExhaustion D) (X : ℕ → Ω → C(D,ℝ))
    (d : ℕ → ℝ) (hd : Summable d)
    (hm : ∀ n, MeasurableSet {ω | d n < compactStageDist K n (X n ω) (X (n+1) ω)})
    (hs : (∑' n, P {ω | d n < compactStageDist K n (X n ω) (X (n+1) ω)}) < ∞) :
    ∀ᵐ ω ∂P, ∃ y : C(D,ℝ), Tendsto (fun n => X n ω) atTop (𝓝 y) := by
  letI (n : ℕ) : CompactSpace (K n) := isCompact_iff_compactSpace.1 (K.isCompact n)
  filter_upwards [Asakura.written_borel_cantelli P
    (fun n => {ω | d n < compactStageDist K n (X n ω) (X (n+1) ω)}) hm hs] with ω hω
  obtain ⟨N,hN⟩ := hω.bddAbove
  have hseq (j) : CauchySeq (fun n => (X n ω).restrict (K j)) := by
    apply cauchySeq_of_summable_dist
    apply hd.of_norm_bounded_eventually_nat
    filter_upwards [eventually_gt_atTop (max N j)] with n hn
    rw [Real.norm_eq_abs,abs_of_nonneg dist_nonneg]
    change compactStageDist K j (X n ω) (X (n+1) ω) ≤ d n
    apply (compact_stage_distance_mono K _ _ ((le_max_right N j).trans hn.le)).trans
    by_contra h
    exact not_le_of_gt ((le_max_left N j).trans_lt hn) (hN (not_le.1 h))
  apply cauchySeq_tendsto_of_complete
  apply compact_stage_cauchy K (fun n => X n ω)
  intro j ε hε
  exact Metric.cauchySeq_iff.1 (hseq j) ε hε

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.compact_stage_distance_mono
#print axioms Asakura.Chapter2Complete.compact_stage_cauchy
#print axioms Asakura.Chapter2Complete.diagonal_compact_increment_limit

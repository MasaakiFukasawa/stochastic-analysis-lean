import FullAuditProgressive
import Mathlib.Order.CompleteLatticeIntervals
import Mathlib.Topology.DenseEmbedding

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.FullAudit
open Asakura.Chapter1Written Asakura.Chapter2Written

/-- The infimum over the countable dense set is the minimum on the compact
 interval. This expands the density step, rather than assuming the infimum identity. -/
theorem compact_dense_distance_zero {K E : Type*} [TopologicalSpace K]
    [CompactSpace K] [Nonempty K] [MetricSpace E]
    (q : ℕ → K) (hq : DenseRange q) (X : K → E) (hX : Continuous X)
    (C : Set E) (hC : IsClosed C) (hne : C.Nonempty) :
    (⨅ n, Metric.infDist (X (q n)) C) = 0 ↔ ∃ s, X s ∈ C := by
  let d := fun s => Metric.infDist (X s) C
  let v := ⨅ n, d (q n)
  have hd : Continuous d := (Metric.continuous_infDist_pt C).comp hX
  have hb : BddBelow (range (fun n => d (q n))) := ⟨0,by rintro y ⟨n,rfl⟩; exact Metric.infDist_nonneg⟩
  have hv (s : K) : v ≤ d s := by
    exact hq.induction_on s (isClosed_le continuous_const hd) (fun n => ciInf_le hb n)
  obtain ⟨s,hs,hmin⟩ := isCompact_univ.exists_isMinOn (univ_nonempty) hd.continuousOn
  have he : v = d s := by
    apply le_antisymm (hv s)
    exact le_ciInf fun n => hmin (mem_univ (q n))
  constructor
  · intro hz
    exact ⟨s,(hC.mem_iff_infDist_zero hne).mpr (he.symm.trans hz)⟩
  · rintro ⟨u,hu⟩
    exact le_antisymm ((hv u).trans_eq (Metric.infDist_zero_of_mem hu))
      (le_ciInf fun n => Metric.infDist_nonneg)

/-- The lower endpoint of a nonempty closed set of hitting times is attained.
 At the terminal time the stopped event is the entire sample space. -/
theorem closed_hitting_lower_event {ι E : Type*} [CompleteLinearOrder ι]
    [TopologicalSpace ι] [OrderTopology ι] [TopologicalSpace E]
    (X : ι → E) (hX : Continuous X) (C : Set E) (hC : IsClosed C)
    (t : ι) (ht : t < ⊤) :
    sInf (X ⁻¹' C) ≤ t ↔ ∃ s ≤ t, X s ∈ C := by
  constructor
  · intro h
    have hn : (X ⁻¹' C).Nonempty := by
      by_contra hn
      rw [not_nonempty_iff_eq_empty.mp hn,sInf_empty] at h
      exact (not_le_of_gt ht) h
    exact ⟨sInf (X ⁻¹' C),h,IsClosed.sInf_mem hn (hC.preimage hX)⟩
  · rintro ⟨s,hs,hC⟩
    exact (sInf_le (show s ∈ X ⁻¹' C from hC)).trans hs

/-- Closed-set hitting times are stopping times, by the manuscript's compact
 distance minimum and countable dense evaluations. Empty target sets and the
 terminal event are handled separately. -/
theorem closed_hitting_stopping_compact {Ω ι E : Type*}
    [CompleteLinearOrder ι] [TopologicalSpace ι] [OrderTopology ι]
    [CompactSpace ι] [SecondCountableTopology ι]
    [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (F : ι → MeasurableSpace Ω) (hF : Monotone F)
    (X : ι → Ω → E) (hm : ∀ t, Measurable[F t] (X t))
    (hc : ∀ ω, Continuous (fun t => X t ω)) (C : Set E) (hC : IsClosed C) :
    ∀ t, MeasurableSet[F t] {ω | sInf {s | X s ω ∈ C} ≤ t} := by
  intro t
  letI : MeasurableSpace Ω := F t
  by_cases htop : t = ⊤
  · simp only [htop,le_top,Set.setOf_true]; exact MeasurableSet.univ
  by_cases hne : C.Nonempty
  swap
  · have he : C = ∅ := not_nonempty_iff_eq_empty.mp hne
    simp only [he,mem_empty_iff_false,Set.setOf_false,sInf_empty,top_le_iff]
    by_cases ht : (⊤ : ι) = t <;> simp [ht]
  letI : Nonempty (Iic t) := ⟨⟨t,le_rfl⟩⟩
  letI : CompactSpace (Iic t) := isCompact_iff_compactSpace.mp (isClosed_Iic : IsClosed (Iic t)).isCompact
  let q := TopologicalSpace.denseSeq (Iic t)
  let d : Ω → ℝ := fun ω => ⨅ n, Metric.infDist (X (q n).val ω) C
  have hd : Measurable d := Measurable.iInf fun n =>
    (Metric.continuous_infDist_pt C).measurable.comp ((hm _).mono (hF (q n).property) le_rfl)
  have he : {ω | sInf {s | X s ω ∈ C} ≤ t} = d ⁻¹' {0} := by
    ext ω
    change sInf ((fun s => X s ω) ⁻¹' C) ≤ t ↔ d ω = 0
    rw [closed_hitting_lower_event (fun s => X s ω) (hc ω) C hC t (lt_top_iff_ne_top.mpr htop)]
    change (∃ s ≤ t, X s ω ∈ C) ↔ (⨅ n, Metric.infDist (X (q n).val ω) C) = 0
    rw [compact_dense_distance_zero q (TopologicalSpace.denseRange_denseSeq _) (fun s : Iic t => X s.val ω)
      ((hc ω).comp continuous_subtype_val) C hC hne]
    constructor
    · rintro ⟨s,hs,h⟩; exact ⟨⟨s,hs⟩,h⟩
    · rintro ⟨s,h⟩; exact ⟨s.val,s.property,h⟩
  rw [he]
  exact hd (measurableSet_singleton 0)

/-- The manuscript's [0,T] time domain, including T=infinity. The infimum in
 this complete interval equals T for an empty hit set, exactly the printed convention. -/
theorem continuous_hitting_stopping_written {Ω E : Type*} {T : EReal} [Fact (0 ≤ T)]
    [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F)
    (X : ClosedTime T → Ω → E) (hm : ∀ t, Measurable[F t] (X t))
    (hc : ∀ ω, Continuous (fun t => X t ω)) (C : Set E) (hC : IsClosed C) :
    ∀ t, MeasurableSet[F t] {ω | sInf {s | X s ω ∈ C} ≤ t} :=
  closed_hitting_stopping_compact F hF X hm hc C hC

end Asakura.FullAudit

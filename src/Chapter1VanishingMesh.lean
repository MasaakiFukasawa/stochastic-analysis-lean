import FullAuditDiscreteVariation
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter1Complete
set_option maxHeartbeats 2000000

lemma set_partition_covers {Ω : Type*} (J : Finpartition (univ : Set Ω)) (x : Ω) :
    ∃ E∈J.parts,x∈E := by
  have h : (⋃ E∈J.parts,E)=univ := by
    rw [← Finset.sup_set_eq_biUnion]
    exact J.sup_parts
  have hx : x∈⋃ E∈J.parts,E := by rw [h]; trivial
  obtain ⟨E,hE⟩ := mem_iUnion.mp hx
  obtain ⟨hE,hx⟩ := mem_iUnion.mp hE
  exact ⟨E,hE,hx⟩

/-- Vanishing mesh is sufficient for interval partitions to generate all
Borel sets: every open set is the countable union of cells contained in it. -/
theorem vanishing_mesh_generates {Ω : Type*} [PseudoMetricSpace Ω]
    [m : MeasurableSpace Ω] [BorelSpace Ω]
    (J : ℕ → Finpartition (univ : Set Ω))
    (hJ : ∀ n,∀ E∈(J n).parts,MeasurableSet E)
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0))
    (hdiam : ∀ n,∀ E∈(J n).parts,∀ x∈E,∀ y∈E,dist x y≤δ n) :
    (⨆ n,MeasurableSpace.generateFrom ((J n).parts : Set (Set Ω)))=m := by
  let G := ⨆ n,MeasurableSpace.generateFrom ((J n).parts : Set (Set Ω))
  have hcell n E (hE : E∈(J n).parts) : MeasurableSet[G] E :=
    (le_iSup (fun n => MeasurableSpace.generateFrom ((J n).parts : Set (Set Ω))) n) E
      (MeasurableSpace.measurableSet_generateFrom hE)
  apply le_antisymm
  · exact iSup_le fun n => MeasurableSpace.generateFrom_le (hJ n)
  · have hb : m=borel Ω := BorelSpace.measurable_eq
    rw [hb]
    apply MeasurableSpace.generateFrom_le
    intro U hU
    change IsOpen U at hU
    have he : U=⋃ n,⋃ E∈(J n).parts,⋃ (_ : E⊆U),E := by
      ext x
      simp only [mem_iUnion]
      constructor
      · intro hx
        obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp hU x hx
        obtain ⟨n,hn⟩ := (hδ.eventually (gt_mem_nhds hε)).exists
        obtain ⟨E,hE,hxE⟩ := set_partition_covers (J n) x
        refine ⟨n,E,hE,?_,hxE⟩
        intro y hy
        apply hball
        exact (hdiam n E hE y hy x hxE).trans_lt hn
      · rintro ⟨n,E,hE,hsub,hx⟩
        exact hsub hx
    rw [he]
    exact MeasurableSet.iUnion fun n => MeasurableSet.biUnion (J n).parts.countable_toSet
      fun E hE => MeasurableSet.iUnion fun _ => hcell n E hE

/-- The preceding chapter theorem applies to actual shrinking measurable
partitions without taking generation of the Borel sigma algebra as a premise. -/
theorem shrinking_partition_variation {Ω : Type*} [PseudoMetricSpace Ω]
    [MeasurableSpace Ω] [BorelSpace Ω]
    (ν : SignedMeasure Ω) (J : ℕ → Finpartition (univ : Set Ω))
    (hJ : ∀ n,∀ E∈(J n).parts,MeasurableSet E) (href : Antitone J)
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0))
    (hdiam : ∀ n,∀ E∈(J n).parts,∀ x∈E,∀ y∈E,dist x y≤δ n) :
    Monotone (fun n => ∑ E∈(J n).parts,|ν E|) ∧
    Tendsto (fun n => ∑ E∈(J n).parts,|ν E|) atTop (𝓝 (ν.totalVariation.real univ)) :=
  Asakura.FullAudit.discrete_variation_written ν J hJ href
    (vanishing_mesh_generates J hJ δ hδ hdiam)

end Asakura.Chapter1Complete

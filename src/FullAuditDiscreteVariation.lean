import FullAuditPartitionRefinement

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.FullAudit

/-- The full signed-measure theorem, following the manuscript's conditional
expectation approximation of each cell of an arbitrary finite partition.
This does not replace that proof by a Radon--Nikodym sign approximation. -/
theorem discrete_variation_written {Ω : Type*} {m : MeasurableSpace Ω}
    (ν : SignedMeasure Ω) (J : ℕ → Finpartition (univ : Set Ω))
    (hJ : ∀ n, ∀ E ∈ (J n).parts, MeasurableSet E)
    (href : Antitone J)
    (hgen : (⨆ n, MeasurableSpace.generateFrom ((J n).parts : Set (Set Ω))) = m) :
    Monotone (fun n => ∑ E ∈ (J n).parts, |ν E|) ∧
    Tendsto (fun n => ∑ E ∈ (J n).parts, |ν E|) atTop (𝓝 (ν.totalVariation.real univ)) := by
  have hmono : Monotone (fun n => ∑ E ∈ (J n).parts, |ν E|) :=
    fun i j hij => discrete_variation_refinement ν (J i) (J j) (hJ j) (href hij)
  refine ⟨hmono, ?_⟩
  have hu := fun n => discrete_variation_upper ν (J n)
  have hn := fun n => Finset.sum_nonneg (s := (J n).parts) (fun E _ => abs_nonneg (ν E))
  by_cases hz : ν.totalVariation univ = 0
  · have hzreal : ν.totalVariation.real univ = 0 := by simp [Measure.real, hz]
    have he (n : ℕ) : (∑ E ∈ (J n).parts, |ν E|) = 0 :=
      le_antisymm ((hu n).trans_eq hzreal) (hn n)
    simpa only [he, hzreal] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 0))
  · let P : Measure Ω := (ν.totalVariation univ)⁻¹ • ν.totalVariation
    have hnorm := variation_normalization ν hz
    letI : IsProbabilityMeasure P := hnorm.1
    have hd : ν.totalVariation ≤ (ν.totalVariation univ) • P := hnorm.2.le
    have hb : BddAbove (range (fun n => ∑ E ∈ (J n).parts, |ν E|)) :=
      ⟨ν.totalVariation.real univ, fun x hx => by obtain ⟨n,rfl⟩ := hx; exact hu n⟩
    let L : ℝ := ⨆ n, ∑ E ∈ (J n).parts, |ν E|
    have hL : Tendsto (fun n => ∑ E ∈ (J n).parts, |ν E|) atTop (𝓝 L) :=
      tendsto_atTop_ciSup hmono hb
    have hLnonneg : 0 ≤ L := (hn 0).trans (le_ciSup hb 0)
    have hupper : L ≤ ν.totalVariation.real univ := ciSup_le hu
    have hlower : ν.totalVariation.real univ ≤ L := by
      apply variation_le_of_partition_bounds ν L hLnonneg
      intro F hF
      exact partition_variation_le_limit P ν (ν.totalVariation univ) (measure_ne_top _ _) hd
        J hJ (fun i j hij => partition_generate_mono (J i) (J j) (href hij)) hgen L hL F hF
    rwa [le_antisymm hupper hlower] at hL

/-- The generating-family formulation printed in the manuscript agrees with
the supremum of the generated finite-partition sigma algebras. -/
theorem partition_generating_union {Ω : Type*} (J : ℕ → Finpartition (univ : Set Ω)) :
    MeasurableSpace.generateFrom (⋃ n, ((J n).parts : Set (Set Ω))) =
      ⨆ n, MeasurableSpace.generateFrom ((J n).parts : Set (Set Ω)) := by
  apply le_antisymm
  · apply MeasurableSpace.generateFrom_le
    intro E hE
    obtain ⟨n,hn⟩ := mem_iUnion.mp hE
    exact (le_iSup (fun n => MeasurableSpace.generateFrom ((J n).parts : Set (Set Ω))) n)
      E (MeasurableSpace.measurableSet_generateFrom hn)
  · apply iSup_le
    intro n
    exact MeasurableSpace.generateFrom_mono (subset_iUnion (fun n : ℕ => ((J n).parts : Set (Set Ω))) n)

end Asakura.FullAudit

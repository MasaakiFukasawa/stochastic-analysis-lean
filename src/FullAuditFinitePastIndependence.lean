import FullAuditTestMeasure

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace Asakura.FullAudit

noncomputable def coordinateSigma {Ω ι : Type*} (X : ι → Ω → ℝ) (J : Finset ι) : MeasurableSpace Ω :=
  MeasurableSpace.comap (fun ω (i : J) => X i.val ω) inferInstance

/-- Enlarging a finite set of coordinates enlarges its sigma algebra. -/
theorem coordinate_sigma_mono {Ω ι : Type*} (X : ι → Ω → ℝ) {J K : Finset ι} (hJK : J ⊆ K) :
    coordinateSigma X J ≤ coordinateSigma X K := by
  letI : MeasurableSpace Ω := coordinateSigma X K
  apply Measurable.comap_le
  apply Measurable.of_eval
  intro j
  exact (measurable_pi_apply (⟨j.val,hJK j.property⟩ : K)).comp
    (Measurable.of_comap_le (show coordinateSigma X K ≤ coordinateSigma X K from le_rfl))

/-- Finite coordinate cylinders generate the sigma algebra of the entire process. -/
theorem coordinate_sigma_iSup {Ω ι : Type*} (X : ι → Ω → ℝ) :
    (⨆ J : Finset ι, coordinateSigma X J) = MeasurableSpace.comap (fun ω i => X i ω) inferInstance := by
  classical
  apply le_antisymm
  · apply iSup_le
    intro J
    letI : MeasurableSpace Ω := MeasurableSpace.comap (fun ω i => X i ω) inferInstance
    apply Measurable.comap_le
    apply Measurable.of_eval
    intro j
    exact (measurable_pi_apply j.val).comp
      (show Measurable[MeasurableSpace.comap (fun ω i => X i ω) inferInstance] (fun ω i => X i ω) from
        Measurable.of_comap_le le_rfl)
  · letI : MeasurableSpace Ω := ⨆ J : Finset ι, coordinateSigma X J
    apply Measurable.comap_le
    apply Measurable.of_eval
    intro i
    let J : Finset ι := {i}
    exact (measurable_pi_apply (⟨i,Finset.mem_singleton_self i⟩ : J)).comp
      (Measurable.of_comap_le (le_iSup (coordinateSigma X) J))

/-- The pi-lambda extension from finite-dimensional independence to the full
process. No uncountable intersection of probability-one events is used. -/
theorem process_independent_of_finite_coordinates {Ω ι : Type*} (G : MeasurableSpace Ω) {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ι → Ω → ℝ)
    (hm : ∀ i, Measurable[m] (X i)) (hG : G ≤ m)
    (h : ∀ J : Finset ι, Indep (coordinateSigma X J) G P) :
    Indep (MeasurableSpace.comap (fun ω i => X i ω) inferInstance) G P := by
  classical
  letI : MeasurableSpace Ω := m
  rw [← coordinate_sigma_iSup]
  apply indep_iSup_of_directed_le h
  · intro J
    exact (Measurable.of_eval (fun i : J => hm i.val)).comap_le
  · exact hG
  · intro J K
    exact ⟨J ∪ K,coordinate_sigma_mono X Finset.subset_union_left,
      coordinate_sigma_mono X Finset.subset_union_right⟩
end Asakura.FullAudit

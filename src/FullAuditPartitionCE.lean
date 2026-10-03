import FullAuditL1Identification
import FullAuditStieltjesSemiring

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.FullAudit

noncomputable def partitionMean {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (J : Finpartition (univ : Set Ω)) (X : Ω → ℝ) : Ω → ℝ :=
  ∑ E ∈ J.parts, E.indicator (fun _ => (P.real E)⁻¹ * ∫ ω in E, X ω ∂P)

/-- On each cell the explicitly constructed mean has the indicated constant value. -/
theorem partitionMean_on_cell {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (J : Finpartition (univ : Set Ω)) (X : Ω → ℝ)
    (E : Set Ω) (hE : E ∈ J.parts) (ω : Ω) (hω : ω ∈ E) :
    partitionMean P J X ω = (P.real E)⁻¹ * ∫ ω in E, X ω ∂P := by
  classical
  simp only [partitionMean, Finset.sum_apply]
  rw [Finset.sum_eq_single E]
  · simp [hω]
  · intro F hF hFE
    have hωF : ω ∉ F := fun h => Set.disjoint_left.mp (J.disjoint hF hE hFE) h hω
    simp [hωF]
  · exact fun h => (h hE).elim

/-- The cells form a pi-system (distinct cells have empty intersection). -/
theorem partition_cells_pi {Ω : Type*} (J : Finpartition (univ : Set Ω)) :
    IsPiSystem (J.parts : Set (Set Ω)) := by
  intro E hE F hF hne
  have heq : E=F := by
    by_contra h
    exact hne.ne_empty (Set.disjoint_iff_inter_eq_empty.mp (J.disjoint hE hF h))
  simpa [heq] using hF

/-- Finite-partition conditional expectation, including cells of probability zero. -/
theorem partitionMean_condExp {Ω : Type*} [m0 : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (J : Finpartition (univ : Set Ω))
    (hJ : ∀ E ∈ J.parts, MeasurableSet E) {X : Ω → ℝ} (hX : Integrable X P) :
    partitionMean P J X =ᵐ[P] P[X | MeasurableSpace.generateFrom (J.parts : Set (Set Ω))] := by
  classical
  let m := MeasurableSpace.generateFrom (J.parts : Set (Set Ω))
  letI : MeasurableSpace Ω := m0
  have hm : m ≤ m0 := MeasurableSpace.generateFrom_le hJ
  have hcell (E : Set Ω) (hE : E ∈ J.parts) : MeasurableSet[m] E :=
    MeasurableSpace.measurableSet_generateFrom hE
  have hYm : Measurable[m] (partitionMean P J X) := by
    change Measurable[m] (fun ω => partitionMean P J X ω)
    simp only [partitionMean, Finset.sum_apply]
    apply Finset.measurable_sum
    intro E hE
    exact measurable_const.indicator (hcell E hE)
  have hYi : Integrable (partitionMean P J X) P := by
    change Integrable (fun ω => partitionMean P J X ω) P
    simp only [partitionMean, Finset.sum_apply]
    apply integrable_finsetSum
    intro E hE
    exact (integrable_const _).indicator (hJ E hE)
  have he (E : Set Ω) (hE : E ∈ J.parts) :
      ∫ ω in E, partitionMean P J X ω ∂P = ∫ ω in E, X ω ∂P := by
    have hy : ∀ᵐ ω ∂P.restrict E, partitionMean P J X ω =
        (P.real E)⁻¹ * ∫ ω in E, X ω ∂P :=
      (ae_restrict_mem (hJ E hE)).mono fun ω hω => partitionMean_on_cell P J X E hE ω hω
    rw [integral_congr_ae hy, setIntegral_const, smul_eq_mul]
    by_cases hz : P.real E = 0
    · have hp : P E = 0 := (measureReal_eq_zero_iff (measure_ne_top P E)).mp hz
      simp [hz, hp]
    · field_simp
  have htot : ∫ ω, partitionMean P J X ω ∂P = ∫ ω, X ω ∂P := by
    have hu : (⋃ E ∈ J.parts, E) = univ := by
      rw [← Finset.sup_set_eq_biUnion]
      exact J.sup_parts
    rw [← setIntegral_univ (f := partitionMean P J X), ← setIntegral_univ (f := X), ← hu,
      integral_biUnion_finset J.parts hJ J.disjoint (fun _ _ => hYi.integrableOn),
      integral_biUnion_finset J.parts hJ J.disjoint (fun _ _ => hX.integrableOn)]
    exact Finset.sum_congr rfl he
  apply ae_eq_condExp_of_forall_setIntegral_eq hm hX
    (fun _ _ _ => hYi.integrableOn) _ hYm.aestronglyMeasurable
  intro A hA _
  refine MeasurableSpace.induction_on_inter (C := fun A _ =>
    ∫ ω in A, partitionMean P J X ω ∂P = ∫ ω in A, X ω ∂P)
    rfl (partition_cells_pi J) ?_ ?_ ?_ ?_ A hA
  · simp
  · exact he
  · intro E hE hEq
    have hy := integral_add_compl (hm _ hE) hYi
    have hx := integral_add_compl (hm _ hE) hX
    linarith
  · intro E hd hme hEq
    rw [integral_iUnion (fun n => hm _ (hme n)) hd hYi.integrableOn,
      integral_iUnion (fun n => hm _ (hme n)) hd hX.integrableOn]
    exact tsum_congr hEq

end Asakura.FullAudit

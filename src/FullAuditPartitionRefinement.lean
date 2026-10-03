import FullAuditVariationApproximation
import Chapter1Variation

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.FullAudit

noncomputable local instance {Ω : Type*} (E : Set Ω) : DecidablePred (fun F : Set Ω => F ⊆ E) :=
  fun _ => Classical.propDecidable _

/-- A coarse cell is the union of all fine cells lying in it. -/
theorem refined_cell_union {Ω : Type*} (J K : Finpartition (univ : Set Ω))
    (hJK : K ≤ J) (E : Set Ω) (hE : E ∈ J.parts) :
    E = ⋃ F ∈ K.parts.filter (fun F => F ⊆ E), F := by
  classical
  ext ω
  constructor
  · intro hω
    have hu : (⋃ F ∈ K.parts, F) = univ := by
      rw [← Finset.sup_set_eq_biUnion]; exact K.sup_parts
    obtain ⟨F,hF,hωF⟩ := mem_iUnion₂.mp (show ω ∈ ⋃ F ∈ K.parts, F by rw [hu]; trivial)
    obtain ⟨E',hE',hFE'⟩ := hJK hF
    have heq : E' = E := by
      by_contra h
      exact Set.disjoint_left.mp (J.disjoint hE' hE h) (hFE' hωF) hω
    exact mem_iUnion₂.mpr ⟨F,Finset.mem_filter.mpr ⟨hF,heq ▸ hFE'⟩,hωF⟩
  · intro h
    rcases mem_iUnion₂.mp h with ⟨F,hF,hωF⟩
    exact (Finset.mem_filter.mp hF).2 hωF

/-- Refining a finite partition increases the generated sigma algebra. -/
theorem partition_generate_mono {Ω : Type*} (J K : Finpartition (univ : Set Ω))
    (hJK : K ≤ J) :
    MeasurableSpace.generateFrom (J.parts : Set (Set Ω)) ≤
      MeasurableSpace.generateFrom (K.parts : Set (Set Ω)) := by
  classical
  apply MeasurableSpace.generateFrom_le
  intro E hE
  rw [refined_cell_union J K hJK E hE]
  exact MeasurableSet.biUnion (Finset.countable_toSet _) fun F hF =>
    MeasurableSpace.measurableSet_generateFrom (Finset.mem_filter.mp hF).1

/-- The total variation bound supplies a finite upper bound for every partition. -/
theorem discrete_variation_upper {Ω : Type*} [MeasurableSpace Ω]
    (ν : SignedMeasure Ω) (J : Finpartition (univ : Set Ω)) :
    ∑ E ∈ J.parts, |ν E| ≤ ν.totalVariation.real univ := by
  have h := Asakura.Chapter1.variation_partition_upper ν J.parts J.disjoint
  have he : (∑ E ∈ J.parts, ‖ν E‖ₑ) = ENNReal.ofReal (∑ E ∈ J.parts, |ν E|) := by
    simp only [← ofReal_norm, Real.norm_eq_abs]
    exact (ENNReal.ofReal_sum_of_nonneg (fun _ _ => abs_nonneg _)).symm
  rw [he] at h
  exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mp h


/-- Forgetting the proof of measurability does not change a finite partition. -/
noncomputable def measurablePartitionForget {Ω : Type*} [MeasurableSpace Ω]
    (F : Finpartition (⟨(univ : Set Ω), MeasurableSet.univ⟩ : Subtype MeasurableSet)) :
    Finpartition (univ : Set Ω) := by
  classical
  refine ⟨F.parts.image Subtype.val, ?_, ?_, ?_⟩
  · apply Finset.supIndep_iff_pairwiseDisjoint.mpr
    intro A hA B hB hAB
    obtain ⟨A',hA',rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨B',hB',rfl⟩ := Finset.mem_image.mp hB
    exact F.pairwiseDisjoint_apply (fun _ _ => rfl) rfl hA' hB' (fun h => hAB (congrArg Subtype.val h))
  · rw [Finset.sup_image]
    exact F.sup_parts_apply (fun _ _ => rfl) rfl
  · intro h
    obtain ⟨A,hA,he⟩ := Finset.mem_image.mp h
    exact F.bot_notMem ((show A = ⊥ from Subtype.ext he) ▸ hA)

/-- Taking the supremum over all finite measurable partitions is the actual
Jordan total variation, not an assumed replacement quantity. -/
theorem variation_le_of_partition_bounds {Ω : Type*} [MeasurableSpace Ω]
    (ν : SignedMeasure Ω) (L : ℝ) (hL : 0 ≤ L)
    (hbound : ∀ F : Finpartition (univ : Set Ω),
      (∀ A ∈ F.parts, MeasurableSet A) → ∑ A ∈ F.parts, |ν A| ≤ L) :
    ν.totalVariation.real univ ≤ L := by
  have ht : ν.totalVariation univ ≤ ENNReal.ofReal L := by
    rw [ν.totalVariation_eq_variation]
    simp only [VectorMeasure.variation_apply, preVariation,
      VectorMeasure.ennrealToMeasure_apply MeasurableSet.univ,
      ennrealPreVariation_apply, preVariationFun, MeasurableSet.univ, dite_true, iSup_le_iff]
    intro F
    have hb := hbound (measurablePartitionForget F) (by
      intro A hA
      obtain ⟨A',hA',rfl⟩ := Finset.mem_image.mp hA
      exact A'.property)
    have he : ∑ A ∈ (measurablePartitionForget F).parts, |ν A| =
        ∑ A ∈ F.parts, |ν (A : Set Ω)| := by
      exact Finset.sum_image (fun _ _ _ _ h => Subtype.ext h)
    rw [he] at hb
    have hs : (∑ A ∈ F.parts, ‖ν (A : Set Ω)‖ₑ) =
        ENNReal.ofReal (∑ A ∈ F.parts, |ν (A : Set Ω)|) := by
      simp only [← ofReal_norm, Real.norm_eq_abs]
      exact (ENNReal.ofReal_sum_of_nonneg (fun _ _ => abs_nonneg _)).symm
    rw [hs]
    exact ENNReal.ofReal_le_ofReal hb
  exact (ENNReal.toReal_mono (ENNReal.ofReal_ne_top) ht).trans_eq (ENNReal.toReal_ofReal hL)


/-- Refinement increases the sum of absolute signed masses, by finite additivity
and the triangle inequality, exactly as at the start of the manuscript proof. -/
theorem discrete_variation_refinement {Ω : Type*} [MeasurableSpace Ω]
    (ν : SignedMeasure Ω) (J K : Finpartition (univ : Set Ω))
    (hK : ∀ F ∈ K.parts, MeasurableSet F) (hJK : K ≤ J) :
    ∑ E ∈ J.parts, |ν E| ≤ ∑ F ∈ K.parts, |ν F| := by
  classical
  have he (E : Set Ω) (hE : E ∈ J.parts) :
      ν E = ∑ F ∈ K.parts, (if F ⊆ E then (1:ℝ) else 0) * ν F := by
    conv_lhs => rw [refined_cell_union J K hJK E hE]
    rw [ν.of_biUnion_finset]
    · simp only [Finset.sum_filter, ite_mul, one_mul, zero_mul]
    · intro A hA B hB hAB
      exact K.disjoint (Finset.mem_filter.mp hA).1 (Finset.mem_filter.mp hB).1 hAB
    · intro F hF
      exact hK F (Finset.mem_filter.mp hF).1
  calc
    _ = ∑ E ∈ J.parts, |∑ F ∈ K.parts, (if F ⊆ E then (1:ℝ) else 0) * ν F| :=
      Finset.sum_congr rfl (fun E hE => congrArg abs (he E hE))
    _ ≤ _ := by
      apply variation_matrix_bound
      · intros; split_ifs <;> norm_num
      · intro F hF
        obtain ⟨E,hE,hFE⟩ := hJK hF
        rw [Finset.sum_eq_single E]
        · simp [hFE]
        · intro A hA hAE
          have hFA : ¬ F ⊆ A := by
            intro hFA
            have hdis : Disjoint F F := (J.disjoint hA hE hAE).mono hFA hFE
            exact K.ne_bot hF (disjoint_self.mp hdis)
          simp [hFA]
        · exact fun h => (h hE).elim

end Asakura.FullAudit

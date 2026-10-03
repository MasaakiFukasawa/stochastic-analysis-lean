import FullAuditJensenContraction
import FullAuditLpComplete

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.FullAudit

/-- Augmentation by every ambient measurable null set transfers measurability
 between almost-everywhere equal ambient measurable representatives. -/
theorem measurable_of_augmented_ae {Ω E : Type*} {m : MeasurableSpace Ω}
    [MeasurableSpace E] [MeasurableEq E] (P : Measure Ω) {G : MeasurableSpace Ω} (hG : G ≤ m)
    (hnull : ∀ N, MeasurableSet[m] N → P N = 0 → MeasurableSet[G] N)
    (f g : Ω → E) (hmf : Measurable[m] f) (hmg : Measurable[G] g)
    (he : f =ᵐ[P] g) [MeasurableSingletonClass E] [TopologicalSpace E] [T2Space E]
    [OpensMeasurableSpace E] : Measurable[G] f := by
  let N := {ω | f ω ≠ g ω}
  have hNm : MeasurableSet[m] N := (measurableSet_eq_fun hmf (hmg.mono hG le_rfl)).compl
  have hNz : P N = 0 := by
    change P {ω | ¬ f ω = g ω} = 0
    exact ae_iff.mp he
  have hNG := hnull N hNm hNz
  intro B hB
  have heq : f ⁻¹' B = (g ⁻¹' B \ N) ∪ (f ⁻¹' B ∩ N) := by
    ext ω
    simp only [mem_preimage,mem_union,Set.mem_sdiff,mem_inter_iff,N,mem_setOf_eq,not_not]
    constructor
    · intro hf
      by_cases h : f ω = g ω
      · exact Or.inl ⟨h ▸ hf,h⟩
      · exact Or.inr ⟨hf,h⟩
    · rintro (⟨hg,h⟩ | ⟨hf,_⟩)
      · exact h ▸ hg
      · exact hf
  rw [heq]
  refine ((hmg hB).diff hNG).union (hnull _ ((hmf hB).inter hNm) ?_)
  exact measure_mono_null inter_subset_right hNz

/-- Identification of an L2 limit with its terminal conditional expectation.
 This uses the checked Jensen contraction and a two-error bound, so no
 almost-everywhere convergent subsequence is needed for this step. -/
theorem conditional_l2_limit_identity {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] {G : MeasurableSpace Ω} (hG : G ≤ m)
    (U V : ℕ → Ω → ℝ) (u v : Ω → ℝ)
    (hU : ∀ n, MemLp (U n) 2 P) (hV : ∀ n, MemLp (V n) 2 P)
    (hu : MemLp u 2 P) (hv : MemLp v 2 P)
    (hc : ∀ n, U n =ᵐ[P] P[V n | G])
    (htu : Tendsto (fun n => eLpNorm (U n-u) 2 P) atTop (𝓝 0))
    (htv : Tendsto (fun n => eLpNorm (V n-v) 2 P) atTop (𝓝 0)) :
    u =ᵐ[P] P[v | G] := by
  letI : MeasurableSpace Ω := m
  have hbound (n : ℕ) : eLpNorm (u-P[v | G]) 2 P ≤
      eLpNorm (U n-u) 2 P + eLpNorm (V n-v) 2 P := by
    have he : U n-P[v | G] =ᵐ[P] P[V n-v | G] := by
      have hsub := condExp_sub ((hV n).integrable (by norm_num)) (hv.integrable (by norm_num)) G
      exact ((hc n).sub EventuallyEq.rfl).trans hsub.symm
    calc
      _ = eLpNorm ((u-U n)+(U n-P[v | G])) 2 P := by congr 1; funext ω; simp
      _ ≤ eLpNorm (u-U n) 2 P + eLpNorm (U n-P[v | G]) 2 P :=
        Asakura.manuscript_minkowski P _ _ 2 (by norm_num)
      _ ≤ eLpNorm (U n-u) 2 P + eLpNorm (V n-v) 2 P := by
        rw [eLpNorm_sub_comm u (U n),eLpNorm_congr_ae he]
        exact add_le_add_right (conditional_lp_contraction_written P hG 2 (by norm_num) (V n-v) ((hV n).sub hv)) _
  have hz : eLpNorm (u-P[v | G]) 2 P = 0 := by
    apply le_antisymm _ zero_le
    have ht : Tendsto (fun n => eLpNorm (U n-u) 2 P+eLpNorm (V n-v) 2 P) atTop (𝓝 0) := by
      simpa only [add_zero] using htu.add htv
    exact le_of_tendsto_of_tendsto tendsto_const_nhds ht (Eventually.of_forall hbound)
  have he := (eLpNorm_eq_zero_iff (by norm_num : (2 : ℝ≥0∞) ≠ 0)).mp hz
  filter_upwards [he] with ω hω
  simpa only [Pi.sub_apply,Pi.zero_apply,sub_eq_zero] using hω

end Asakura.FullAudit

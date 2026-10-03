import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
import Mathlib.MeasureTheory.Measure.Restrict

open MeasureTheory Set
open scoped ENNReal
namespace Asakura.Chapter2Complete
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

variable {S : Type*} [MeasurableSpace S]

theorem disjoint_sum_restrict (μ : ℕ → Measure S) (B : ℕ → Set S)
    (hB : ∀ n, MeasurableSet (B n)) (hd : Pairwise (fun i j => Disjoint (B i) (B j))) (j : ℕ) :
    (Measure.sum (fun n => (μ n).restrict (B n))).restrict (B j) = (μ j).restrict (B j) := by
  ext s hs
  rw [Measure.restrict_apply hs,Measure.sum_apply _ (hs.inter (hB j))]
  rw [tsum_eq_single j]
  · rw [Measure.restrict_apply (hs.inter (hB j)),Measure.restrict_apply hs]
    simp only [inter_assoc,inter_self]
  · intro i hij
    rw [Measure.restrict_apply (hs.inter (hB j))]
    have he : (s ∩ B j) ∩ B i = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact Set.disjoint_left.mp (hd hij) hx.2 hx.1.2
    rw [he,measure_empty]

/-- Countably many sigma-finite pieces can be pasted on disjoint measurable
regions. Unlike an unrestricted sum, this preserves sigma-finiteness. -/
theorem disjoint_sum_sigmaFinite (μ : ℕ → Measure S) [∀ n, SigmaFinite (μ n)]
    (B : ℕ → Set S) (hB : ∀ n, MeasurableSet (B n))
    (hd : Pairwise (fun i j => Disjoint (B i) (B j))) :
    SigmaFinite (Measure.sum (fun n => (μ n).restrict (B n))) := by
  classical
  let ν := Measure.sum (fun n => (μ n).restrict (B n))
  let D := (⋃ n, B n)ᶜ
  have hD : MeasurableSet D := (MeasurableSet.iUnion hB).compl
  have hz : ν D = 0 := by
    rw [Measure.sum_apply _ hD]
    apply ENNReal.tsum_eq_zero.mpr
    intro i
    rw [Measure.restrict_apply hD]
    have he : D ∩ B i = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact hx.1 (mem_iUnion.mpr ⟨i,hx.2⟩)
    rw [he,measure_empty]
  let C := fun p : ℕ × ℕ => (B p.1 ∩ spanningSets (μ p.1) p.2) ∪ D
  have hfin p : ν (C p) < ∞ := by
    apply lt_of_le_of_lt (measure_union_le _ _) _
    rw [hz,add_zero]
    have he := congrArg (fun η : Measure S => η (spanningSets (μ p.1) p.2)) (disjoint_sum_restrict μ B hB hd p.1)
    rw [Measure.restrict_apply (measurableSet_spanningSets _ _),
      Measure.restrict_apply (measurableSet_spanningSets _ _)] at he
    rw [inter_comm,he]
    exact (measure_mono inter_subset_left).trans_lt (measure_spanningSets_lt_top (μ p.1) p.2)
  apply Measure.sigmaFinite_of_countable (countable_range C)
  · rintro s ⟨p,rfl⟩
    exact hfin p
  · apply eq_univ_of_forall
    intro x
    by_cases hx : x ∈ ⋃ n, B n
    · obtain ⟨n,hn⟩ := mem_iUnion.mp hx
      have hmem : x ∈ ⋃ k, spanningSets (μ n) k := by rw [iUnion_spanningSets]; exact mem_univ _
      obtain ⟨k,hk⟩ := mem_iUnion.mp hmem
      exact mem_sUnion.mpr ⟨C (n,k),mem_range_self _,Or.inl ⟨hn,hk⟩⟩
    · exact mem_sUnion.mpr ⟨C (0,0),mem_range_self _,Or.inr hx⟩

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.disjoint_sum_sigmaFinite

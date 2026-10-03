import Chapter2BoundedL2Convergence
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Function.LpSpace.Complete

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

variable {E S : Type*} [MeasurableSpace E] [MeasurableSpace S]

noncomputable def setL2 (ν : Measure S) [IsFiniteMeasure ν]
    (s : Set S) (hs : MeasurableSet s) : Lp ℝ 2 ν :=
  ((memLp_const (1 : ℝ)).indicator hs).toLp (s.indicator (fun _ => (1:ℝ)))

theorem setL2_empty (ν : Measure S) [IsFiniteMeasure ν] :
    setL2 ν ∅ .empty = 0 := by
  unfold setL2
  simp only [indicator_empty]
  exact MemLp.toLp_zero _

theorem setL2_compl (ν : Measure S) [IsFiniteMeasure ν]
    (s : Set S) (hs : MeasurableSet s) :
    setL2 ν sᶜ hs.compl = setL2 ν univ .univ - setL2 ν s hs := by
  classical
  unfold setL2
  rw [← MemLp.toLp_sub]
  apply MemLp.toLp_congr
  exact ae_of_all _ (fun r => by by_cases h : r ∈ s <;> simp [h])

theorem setL2_union (ν : Measure S) [IsFiniteMeasure ν]
    (s t : Set S) (hs : MeasurableSet s) (ht : MeasurableSet t) (hd : Disjoint s t) :
    setL2 ν (s ∪ t) (hs.union ht) = setL2 ν s hs + setL2 ν t ht := by
  unfold setL2
  rw [← MemLp.toLp_add]
  apply MemLp.toLp_congr
  exact ae_of_all _ (fun r => congrFun (Set.indicator_union_of_disjoint hd _) r)

/-- Joint measurability of an indicator implies strong measurability of its
L2-valued sections, without a separability assumption on the underlying space. -/
theorem stronglyMeasurable_setL2_sections
    (ν : Measure S) [IsFiniteMeasure ν] (s : Set (E × S)) (hs : MeasurableSet s) :
    StronglyMeasurable (fun x => setL2 ν (Prod.mk x ⁻¹' s) (measurable_prodMk_left hs)) := by
  classical
  induction s, hs using MeasurableSpace.induction_on_inter generateFrom_prod.symm isPiSystem_prod with
  | empty => simpa only [preimage_empty,setL2_empty] using (stronglyMeasurable_const : StronglyMeasurable (fun _ : E => (0 : Lp ℝ 2 ν)))
  | basic s hs =>
    obtain ⟨s, hs, t, ht, rfl⟩ := hs
    have he : (fun x => setL2 ν (Prod.mk x ⁻¹' (s ×ˢ t)) (measurable_prodMk_left (hs.prod ht))) =
        s.indicator (fun _ => setL2 ν t ht) := by
      funext x
      by_cases hx : x ∈ s
      · simp [mk_preimage_prod_right_eq_if,hx]
      · simp [mk_preimage_prod_right_eq_if,hx,setL2_empty]
    rw [he]
    exact stronglyMeasurable_const.indicator hs
  | compl s hs ih =>
    have he : (fun x => setL2 ν (Prod.mk x ⁻¹' sᶜ) (measurable_prodMk_left hs.compl)) =
        fun x => setL2 ν univ .univ - setL2 ν (Prod.mk x ⁻¹' s) (measurable_prodMk_left hs) := by
      funext x
      exact setL2_compl ν _ (measurable_prodMk_left hs)
    rw [he]
    exact stronglyMeasurable_const.sub ih
  | iUnion f hd hm ih =>
    let u (n : ℕ) : Set (E × S) := ⋃ k ∈ Finset.range n, f k
    have hu n : MeasurableSet (u n) := MeasurableSet.biUnion (to_countable _) (fun k _ => hm k)
    have hsm n : StronglyMeasurable (fun x => setL2 ν (Prod.mk x ⁻¹' u n) (measurable_prodMk_left (hu n))) := by
      induction n with
      | zero => simpa [u,setL2_empty] using (stronglyMeasurable_const : StronglyMeasurable (fun _ : E => (0 : Lp ℝ 2 ν)))
      | succ n hn =>
        have he : u (n+1) = u n ∪ f n := by
          ext z
          simp only [u,mem_iUnion,Finset.mem_range,mem_union]
          constructor
          · rintro ⟨k,hk,hz⟩
            by_cases hkn : k < n
            · exact Or.inl ⟨k,hkn,hz⟩
            · have : k = n := by omega
              exact Or.inr (this ▸ hz)
          · rintro (⟨k,hk,hz⟩|hz)
            · exact ⟨k,by omega,hz⟩
            · exact ⟨n,by omega,hz⟩
        have hdis : Disjoint (u n) (f n) := by
          apply disjoint_iUnion_left.mpr
          intro k
          apply disjoint_iUnion_left.mpr
          intro hk
          exact hd (ne_of_lt (Finset.mem_range.mp hk))
        have he' : (fun x => setL2 ν (Prod.mk x ⁻¹' u (n+1)) (measurable_prodMk_left (hu (n+1)))) =
            fun x => setL2 ν (Prod.mk x ⁻¹' u n) (measurable_prodMk_left (hu n)) +
              setL2 ν (Prod.mk x ⁻¹' f n) (measurable_prodMk_left (hm n)) := by
          funext x
          simp only [he,preimage_union,setL2_union ν _ _ (measurable_prodMk_left (hu n)) (measurable_prodMk_left (hm n)) (hdis.preimage (Prod.mk x))]
        rw [he']
        exact hn.add (ih n)
    apply stronglyMeasurable_of_tendsto atTop hsm
    apply tendsto_pi_nhds.mpr
    intro x
    apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ _ _ _).mpr
    apply bounded_l2_ae_convergence ν _ _ 1 (by norm_num)
    · intro n; exact (measurable_const.indicator (measurable_prodMk_left (hu n))).aestronglyMeasurable
    · exact (measurable_const.indicator (measurable_prodMk_left (MeasurableSet.iUnion hm))).aestronglyMeasurable
    · intro n; exact ae_of_all _ (fun r => by by_cases h : (x,r) ∈ u n <;> simp [h])
    · exact ae_of_all _ (fun r => by
        exact norm_indicator_le_norm_self _ r |>.trans (by norm_num))
    · apply ae_of_all
      intro r
      by_cases h : (x,r) ∈ ⋃ n, f n
      · obtain ⟨k,hk⟩ := mem_iUnion.mp h
        apply tendsto_const_nhds.congr'
        filter_upwards [eventually_ge_atTop (k+1)] with n hn
        have hkn : k ∈ Finset.range n := Finset.mem_range.mpr (by omega)
        have hun : (x,r) ∈ u n := mem_iUnion.mpr ⟨k,mem_iUnion.mpr ⟨hkn,hk⟩⟩
        have hr : r ∈ Prod.mk x ⁻¹' ⋃ i, f i := h
        have hrn : r ∈ Prod.mk x ⁻¹' u n := hun
        rw [indicator_of_mem hr,indicator_of_mem hrn]
      · have hun n : (x,r) ∉ u n := by
          intro hh
          obtain ⟨k,hk⟩ := mem_iUnion.mp hh
          obtain ⟨_,hk⟩ := mem_iUnion.mp hk
          exact h (mem_iUnion.mpr ⟨k,hk⟩)
        have hr : r ∉ Prod.mk x ⁻¹' ⋃ i, f i := h
        have hrn n : r ∉ Prod.mk x ⁻¹' u n := hun n
        simpa only [indicator_of_notMem (hrn _),indicator_of_notMem hr] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 0))

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.stronglyMeasurable_setL2_sections

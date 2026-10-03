import Chapter12MonotoneClassLpDensity

open Set Filter MeasureTheory MeasurableSpace
open scoped Topology ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

/-- Closed linear subspaces containing the indicators of a generating
pi-system and the constant one contain every finite-Lp function. The proof
uses the monotone-class theorem, then simple-function approximation. -/
theorem lp_closed_subspace_of_generating_pi {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (p : ℝ≥0∞) [Fact (1≤p)] (hp : p≠⊤)
    (C : Set (Set Ω)) (hC : IsPiSystem C) (hgen : m=generateFrom C)
    (V : Submodule ℝ (Lp ℝ p P)) (hV : IsClosed (V : Set (Lp ℝ p P)))
    (hu : indicatorConstLp p MeasurableSet.univ (measure_ne_top P _) (1:ℝ)∈V)
    (hc : ∀ s∈C,∀ hs : MeasurableSet s,indicatorConstLp p hs (measure_ne_top P s) (1:ℝ)∈V) :
    ∀ f : Lp ℝ p P,f∈V := by
  classical
  let I (s : Set Ω) (hs : MeasurableSet s) : Lp ℝ p P :=
    indicatorConstLp p hs (measure_ne_top P s) (1:ℝ)
  have hall : ∀ s (hs : MeasurableSet s),I s hs∈V := by
    refine MeasurableSpace.induction_on_inter (C := fun s hs => I s hs∈V) hgen hC ?_ ?_ ?_ ?_
    · simpa [I] using V.zero_mem
    · exact fun s hs => hc s hs _
    · intro s hs hmem
      have he : I sᶜ hs.compl=I univ MeasurableSet.univ-I s hs := by
        apply Lp.ext
        filter_upwards [indicatorConstLp_coeFn (p := p) (hs := hs.compl) (hμs := measure_ne_top P _) (c := (1:ℝ)),
          Lp.coeFn_sub (I univ MeasurableSet.univ) (I s hs),
          indicatorConstLp_coeFn (p := p) (hs := MeasurableSet.univ) (hμs := measure_ne_top P _) (c := (1:ℝ)),
          indicatorConstLp_coeFn (p := p) (hs := hs) (hμs := measure_ne_top P _) (c := (1:ℝ))] with w h1 h2 h3 h4
        change (I sᶜ hs.compl) w=(I univ MeasurableSet.univ-I s hs) w
        rw [h1,h2]
        change _=(I univ MeasurableSet.univ) w-(I s hs) w
        rw [h3,h4]
        by_cases hw : w∈s <;> simp [hw]
      rw [he]
      exact V.sub_mem hu hmem
    · intro f hd hf hmem
      let A (n : ℕ) := ⋃ i∈Finset.range n,f i
      have hmA : ∀ n,MeasurableSet (A n) := fun n => MeasurableSet.iUnion (fun i => MeasurableSet.iUnion (fun _ => hf i))
      have hIA : ∀ n,I (A n) (hmA n)∈V := by
        intro n
        induction n with
        | zero => simpa [A,I] using V.zero_mem
        | succ n hn =>
          have he : A (n+1)=A n∪f n := by
            ext w
            simp only [A,mem_iUnion,Finset.mem_range,exists_prop,mem_union]
            constructor
            · rintro ⟨i,hi,hwi⟩
              by_cases he : i=n
              · exact Or.inr (he ▸ hwi)
              · exact Or.inl ⟨i,by omega,hwi⟩
            · rintro (⟨i,hi,hwi⟩ | hn)
              · exact ⟨i,by omega,hwi⟩
              · exact ⟨n,by omega,hn⟩
          have hdA : Disjoint (A n) (f n) := by
            apply disjoint_iUnion_left.mpr
            intro i
            apply disjoint_iUnion_left.mpr
            intro hi
            exact hd (ne_of_lt (Finset.mem_range.mp hi))
          have hh := indicatorConstLp_disjoint_union (p := p) (hmA n) (hf n)
            (measure_ne_top P _) (measure_ne_top P _) hdA (1:ℝ)
          have heI : I (A (n+1)) (hmA (n+1))=I (A n) (hmA n)+I (f n) (hf n) := by
            simpa only [he,I] using hh
          rw [heI]
          exact V.add_mem hn (hmem n)
      have hlim : ∀ w,Tendsto (fun n => (A n).indicator (fun _ => (1:ℝ)) w) atTop
          (𝓝 ((⋃ i,f i).indicator (fun _ => (1:ℝ)) w)) := by
        intro w
        by_cases hw : w∈⋃ i,f i
        · obtain ⟨i,hi⟩ := mem_iUnion.mp hw
          apply tendsto_const_nhds.congr'
          filter_upwards [eventually_ge_atTop (i+1)] with n hn
          have hwa : w∈A n := mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨Finset.mem_range.mpr (by omega),hi⟩⟩
          simp [hwa,hw]
        · have hwa : ∀ n,w∉A n := by
            intro n hn
            obtain ⟨i,hi⟩ := mem_iUnion.mp hn
            obtain ⟨_,hi⟩ := mem_iUnion.mp hi
            exact hw (mem_iUnion.mpr ⟨i,hi⟩)
          simpa [hwa,hw] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 0))
      have hLpA := fun n => (memLp_const (1:ℝ) (p := p) (μ := P)).indicator (hmA n)
      have hLpU := (memLp_const (1:ℝ) (p := p) (μ := P)).indicator (MeasurableSet.iUnion hf)
      have hlp := dominated_Lp_limit P p (Fact.out) hp _ _ (fun _ => (1:ℝ)) (memLp_const 1)
        (fun n => (hLpA n).aestronglyMeasurable) hLpU
        (fun n => ae_of_all _ (fun w => by by_cases hw : w∈A n <;> simp [hw]))
        (ae_of_all _ hlim)
      have ht := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ hLpA _ hLpU).mpr hlp
      exact hV.mem_of_tendsto ht (Filter.Eventually.of_forall hIA)
  apply lp_closed_subspace_of_dense_sets P p hp univ dense_univ V hV
  intro s _
  exact hall s s.property

end Asakura.Chapter12

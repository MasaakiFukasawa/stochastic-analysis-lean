import Chapter12SmoothIntervalIndicator

open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

noncomputable def smoothRectangleIndicator {ι : Type*} [Fintype ι]
    (a b : ι → ℝ) (n : ℕ) (x : ι → ℝ) : ℝ := ∏ i,smoothIntervalIndicator (a i) (b i) n (x i)

theorem smooth_rectangle_bounds {ι : Type*} [Fintype ι]
    (a b : ι → ℝ) (n : ℕ) (x : ι → ℝ) :
    0≤smoothRectangleIndicator a b n x ∧ smoothRectangleIndicator a b n x≤1 := by
  refine ⟨Finset.prod_nonneg (fun i _ => (smooth_interval_bounds (a i) (b i) n (x i)).1),?_⟩
  have he := Finset.prod_le_prod₀
    (fun i (_ : i∈(Finset.univ : Finset ι)) => (smooth_interval_bounds (a i) (b i) n (x i)).1)
    (fun i (_ : i∈(Finset.univ : Finset ι)) => (smooth_interval_bounds (a i) (b i) n (x i)).2)
  simpa only [Finset.prod_const_one,smoothRectangleIndicator] using he

theorem smooth_rectangle_contDiff {ι : Type*} [Fintype ι]
    (a b : ι → ℝ) (n : ℕ) : ContDiff ℝ ∞ (smoothRectangleIndicator a b n) := by
  apply contDiff_prod
  intro i _
  exact (smooth_interval_contDiff (a i) (b i) n).comp (contDiff_apply ℝ ℝ i)

theorem smooth_rectangle_compact {ι : Type*} [Fintype ι]
    (a b : ι → ℝ) (n : ℕ) : HasCompactSupport (smoothRectangleIndicator a b n) := by
  classical
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_univ_pi (fun i => isCompact_Icc (a := a i) (b := b i)))
  intro x hx
  apply mem_univ_pi.mpr
  intro i
  by_contra hi
  have ho : x i∉Ioo (a i) (b i) := fun h => hi ⟨h.1.le,h.2.le⟩
  have hz : smoothRectangleIndicator a b n x=0 :=
    Finset.prod_eq_zero (Finset.mem_univ i) (smooth_interval_zero (a i) (b i) n (x i) ho)
  exact hx hz

theorem smooth_rectangle_indicator_limit {ι : Type*} [Fintype ι]
    (a b x : ι → ℝ) :
    Tendsto (fun n => smoothRectangleIndicator a b n x) atTop
      (𝓝 ((Set.pi univ (fun i => Ioo (a i) (b i))).indicator (fun _ => (1:ℝ)) x)) := by
  classical
  have ht := tendsto_finsetProd Finset.univ (fun i _ => smooth_interval_indicator_limit (a i) (b i) (x i))
  have he : (∏ i,(Ioo (a i) (b i)).indicator (fun _ => (1:ℝ)) (x i))=
      (Set.pi univ (fun i => Ioo (a i) (b i))).indicator (fun _ => (1:ℝ)) x := by
    by_cases hx : x∈Set.pi univ (fun i => Ioo (a i) (b i))
    · rw [indicator_of_mem hx]
      simp only [indicator_of_mem (mem_univ_pi.mp hx _),Finset.prod_const_one]
    · rw [indicator_of_notMem hx]
      have hh : ∃ i,x i∉Ioo (a i) (b i) := by simpa only [Set.mem_pi,mem_univ,true_implies,not_forall] using hx
      obtain ⟨i,hi⟩ := hh
      exact Finset.prod_eq_zero (Finset.mem_univ i) (indicator_of_notMem hi _)
  simpa only [smoothRectangleIndicator,he] using ht

/-- Smoothing the rectangle boundary gives the manuscript's finite-dimensional
Lp approximation. It holds for any finite law; Gaussian boundary nullity
allows replacement by closed or half-closed rectangles as well. -/
theorem smooth_rectangle_Lp_limit {ι : Type*} [Fintype ι]
    (ν : Measure (ι → ℝ)) [IsFiniteMeasure ν] (a b : ι → ℝ)
    (p : ℝ≥0∞) (hp : 1≤p) (hpt : p≠⊤) :
    Tendsto (fun n => eLpNorm
      (smoothRectangleIndicator a b n-(Set.pi univ (fun i => Ioo (a i) (b i))).indicator (fun _ => (1:ℝ))) p ν)
      atTop (𝓝 0) := by
  have hm : MeasurableSet (Set.pi univ (fun i => Ioo (a i) (b i))) := MeasurableSet.pi (Set.to_countable _) (fun i _ => measurableSet_Ioo)
  apply dominated_Lp_limit ν p hp hpt _ _ (fun _ => (1:ℝ)) (memLp_const 1)
    (fun n => (smooth_rectangle_contDiff a b n).continuous.aestronglyMeasurable)
    ((memLp_const 1).indicator hm)
  · intro n
    filter_upwards [] with x
    simpa only [Real.norm_eq_abs,abs_one,abs_of_nonneg (smooth_rectangle_bounds a b n x).1]
      using (smooth_rectangle_bounds a b n x).2
  · exact ae_of_all _ (fun x => smooth_rectangle_indicator_limit a b x)

end Asakura.Chapter12

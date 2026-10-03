import Chapter4PicardFatou

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter4.Vector
variable {dim : ℕ}
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false

/-- The absolute uniform Picard limit can be chosen continuously and adapted
on one common null set. No adaptedness of the limit is assumed. -/
theorem adapted_picard_series_limit
    {Ω D : Type*} {m : MeasurableSpace Ω}
    [MetricSpace D] [CompactSpace D] [SecondCountableTopology D]
    (P : Measure Ω) [IsProbabilityMeasure P] (F : D → MeasurableSpace Ω)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (Z : ℕ → Ω → C(D,Fin dim → ℝ)) (hZ : ∀ n, Measurable[m] (Z n))
    (ha : ∀ n t, Measurable[F t] (fun ω => Z n ω t))
    (A a : ℝ) (ha0 : 0 ≤ a)
    (hb : ∀ n, eLpNorm (Z n) 2 P ≤ ENNReal.ofReal (A*Real.sqrt (a^n/(n.factorial:ℝ)))) :
    ∃ Y : Ω → C(D,Fin dim → ℝ), Measurable[m] Y ∧
      (∀ t, Measurable[F t] (fun ω => Y ω t)) ∧
      ∀ᵐ ω ∂P, Tendsto (fun n => ∑ k ∈ Finset.range n, Z k ω) atTop (𝓝 (Y ω)) := by
  classical
  let S := fun n ω => ∑ k ∈ Finset.range n, Z k ω
  have hS n : Measurable[m] (S n) := Finset.measurable_sum _ (fun k _ => hZ k)
  have hlim : ∀ᵐ ω ∂P, ∃ y, Tendsto (fun n => S n ω) atTop (𝓝 y) := by
    filter_upwards [picard_path_series P Z (fun n => (hZ n).aestronglyMeasurable) A a ha0 hb] with ω hω
    exact ⟨∑' n, Z n ω,hω.2.hasSum.tendsto_sum_nat⟩
  obtain ⟨N,Y,hN,hNP,hY,hall⟩ :=
    Asakura.Chapter2Complete.measurable_limit_after_null_modification P 0 S hS hlim
  refine ⟨Y,hY,?_,?_⟩
  · intro t
    letI : MeasurableSpace Ω := F t
    have hSm n : Measurable (fun ω => if ω ∈ N then (0 : Fin dim → ℝ) else S n ω t) := by
      apply Measurable.ite (hnull t N hN hNP) measurable_const
      simpa only [S,ContinuousMap.sum_apply] using
        (Finset.measurable_sum (Finset.range n) (fun k _ => ha k t))
    apply measurable_of_tendsto_metrizable hSm
    apply tendsto_pi_nhds.mpr
    intro ω
    have hh := (continuous_eval_const t : Continuous (fun f : C(D,Fin dim → ℝ) => f t)).continuousAt.tendsto.comp (hall ω)
    by_cases hω : ω ∈ N
    · simpa [Function.comp_def,hω] using hh
    · simpa [Function.comp_def,hω] using hh
  · have hn : ∀ᵐ ω ∂P, ω ∉ N := by rw [ae_iff]; simpa using hNP
    filter_upwards [hn] with ω hω
    simpa only [if_neg hω,S] using hall ω

/-- Combine the pathwise construction with the Fatou argument for the
actual factorial bounds of the Picard iteration. -/
theorem adapted_picard_series_L2_limit
    {Ω D : Type*} {m : MeasurableSpace Ω}
    [MetricSpace D] [CompactSpace D] [SecondCountableTopology D]
    (P : Measure Ω) [IsProbabilityMeasure P] (F : D → MeasurableSpace Ω)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (Z : ℕ → Ω → C(D,Fin dim → ℝ)) (hZ : ∀ n, Measurable[m] (Z n))
    (ha : ∀ n t, Measurable[F t] (fun ω => Z n ω t))
    (A a : ℝ) (ha0 : 0 ≤ a)
    (hb : ∀ n, eLpNorm (Z n) 2 P ≤ ENNReal.ofReal (A*Real.sqrt (a^n/(n.factorial:ℝ)))) :
    ∃ Y : Ω → C(D,Fin dim → ℝ), Measurable[m] Y ∧
      (∀ t, Measurable[F t] (fun ω => Y ω t)) ∧ MemLp Y 2 P ∧
      (∀ᵐ ω ∂P, Tendsto (fun n => ∑ k ∈ Finset.range n, Z k ω) atTop (𝓝 (Y ω))) ∧
      Tendsto (fun n => eLpNorm (fun ω => Y ω-∑ k ∈ Finset.range n, Z k ω) 2 P) atTop (𝓝 0) := by
  obtain ⟨Y,hYm,hYa,hlim⟩ := adapted_picard_series_limit P F hnull Z hZ ha A a ha0 hb
  have hsum := ((summable_sqrt_factorial a ha0).mul_left A).tsum_ofReal_lt_top
  have hs : (∑' n, eLpNorm (Z n) 2 P) ≠ ∞ :=
    ((ENNReal.tsum_le_tsum hb).trans_lt hsum).ne
  have hf := picard_fatou_tail P Z (fun n => (hZ n).aestronglyMeasurable) Y hYm.aestronglyMeasurable hs hlim
  exact ⟨Y,hYm,hYa,hf.1,hlim,hf.2.2⟩

/-- Restore the initial path to the convergent increment series. The output
is the limit of the actual iterates, simultaneously adapted, continuous,
and L2-convergent. -/
theorem adapted_picard_iterates_limit
    {Ω D : Type*} {m : MeasurableSpace Ω}
    [MetricSpace D] [CompactSpace D] [SecondCountableTopology D]
    (P : Measure Ω) [IsProbabilityMeasure P] (F : D → MeasurableSpace Ω)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X : ℕ → Ω → C(D,Fin dim → ℝ)) (hm : ∀ n, Measurable[m] (X n))
    (ha : ∀ n t, Measurable[F t] (fun ω => X n ω t))
    (hi : MemLp (X 0) 2 P) (A a : ℝ) (ha0 : 0 ≤ a)
    (hb : ∀ n, eLpNorm (fun ω => X (n+1) ω-X n ω) 2 P ≤
      ENNReal.ofReal (A*Real.sqrt (a^n/(n.factorial:ℝ)))) :
    ∃ Y : Ω → C(D,Fin dim → ℝ), Measurable[m] Y ∧
      (∀ t, Measurable[F t] (fun ω => Y ω t)) ∧ MemLp Y 2 P ∧
      (∀ᵐ ω ∂P, Tendsto (fun n => X n ω) atTop (𝓝 (Y ω))) ∧
      Tendsto (fun n => eLpNorm (fun ω => Y ω-X n ω) 2 P) atTop (𝓝 0) := by
  let Z : ℕ → Ω → C(D,Fin dim → ℝ) := fun n ω => X (n+1) ω-X n ω
  have hZm n : Measurable[m] (Z n) := (hm (n+1)).sub (hm n)
  have hZa n t : Measurable[F t] (fun ω => Z n ω t) := by
    change Measurable[F t] (fun ω => X (n+1) ω t-X n ω t)
    exact (ha (n+1) t).sub (ha n t)
  obtain ⟨Y,hYm,hYa,hYi,hlim,hL2⟩ := adapted_picard_series_L2_limit P F hnull Z
    hZm hZa A a ha0 hb
  have hsum n ω : (∑ k ∈ Finset.range n, Z k ω) = X n ω-X 0 ω :=
    Finset.sum_range_sub (fun k => X k ω) n
  refine ⟨fun ω => X 0 ω+Y ω,?_,?_,?_,?_,?_⟩
  · exact (hm 0).add hYm
  · intro t
    change Measurable[F t] (fun ω => X 0 ω t+Y ω t)
    exact (ha 0 t).add (hYa t)
  · exact MemLp.add (f := X 0) (g := Y) (p := 2) (μ := P) hi hYi
  · filter_upwards [hlim] with ω hω
    have h := (tendsto_const_nhds (x := X 0 ω) (f := atTop)).add hω
    have he n : X 0 ω+(∑ k ∈ Finset.range n, Z k ω) = X n ω := by
      rw [hsum]
      abel
    simpa only [he] using h
  · have he n : (fun ω => X 0 ω+Y ω-X n ω) =
        (fun ω => Y ω-∑ k ∈ Finset.range n, Z k ω) := by
      funext ω
      rw [hsum]
      abel
    simpa only [← he] using hL2


end Asakura.Chapter4.Vector

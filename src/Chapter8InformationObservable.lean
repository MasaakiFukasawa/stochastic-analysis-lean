import Chapter8UnboundedTimeAverage

open MeasureTheory Set Filter Finset
open scoped Topology BigOperators NNReal
namespace Asakura.Chapter8
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- Every Gram entry is C1 and integrable under a finite-second-moment
law when the coefficient columns are C1 and globally Lipschitz. -/
theorem information_entry_regular {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
    (π : Measure E) [IsProbabilityMeasure π] (hπ : MemLp (fun x : E => x) 2 π)
    {d : ℕ} (f g : Fin d → E → ℝ) (L K : Fin d → ℝ≥0)
    (hf : ∀ j,LipschitzWith (L j) (f j)) (hg : ∀ j,LipschitzWith (K j) (g j))
    (hfc : ∀ j,ContDiff ℝ 1 (f j)) (hgc : ∀ j,ContDiff ℝ 1 (g j)) :
    ContDiff ℝ 1 (fun x => ∑ j,f j x*g j x) ∧
      Integrable (fun x => ∑ j,f j x*g j x) π := by
  constructor
  · apply ContDiff.sum
    intro j _
    exact (hfc j).mul (hgc j)
  · apply integrable_finset_sum
    intro j _
    exact (lipschitz_observable_memLp π id hπ (f j) (L j) (hf j)).integrable_mul
      (lipschitz_observable_memLp π id hπ (g j) (K j) (hg j))

/-- Apply the actual smooth-cutoff argument to a Gram information entry. -/
theorem information_stationary_L1_limit {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P] (π : Measure E) [IsProbabilityMeasure π]
    (hπ : MemLp (fun x : E => x) 2 π)
    (Y : Ω → ℝ → E) (hY : Measurable (Function.uncurry Y))
    (hcY : ∀ w,Continuous (Y w)) (hlaw : ∀ t,P.map (fun w => Y w t)=π)
    (T : ℕ → ℝ) (hT : ∀ n,0<T n)
    (hlim : ∀ (g : E → ℝ) (L : ℝ≥0),LipschitzWith L g →
      (∃ K : ℝ,0 ≤ K ∧ ∀ x,|g x| ≤ K) →
      Tendsto (fun n => ∫ w,|Asakura.FullAudit.timeAverage (fun t => g (Y w t)) (T n)-(∫ x,g x ∂π)| ∂P)
        atTop (nhds 0))
    {d : ℕ} (f g : Fin d → E → ℝ) (L K : Fin d → ℝ≥0)
    (hf : ∀ j,LipschitzWith (L j) (f j)) (hg : ∀ j,LipschitzWith (K j) (g j))
    (hfc : ∀ j,ContDiff ℝ 1 (f j)) (hgc : ∀ j,ContDiff ℝ 1 (g j)) :
    Tendsto (fun n => ∫ w,|Asakura.FullAudit.timeAverage (fun t => ∑ j,f j (Y w t)*g j (Y w t)) (T n)-
      (∫ x,∑ j,f j x*g j x ∂π)| ∂P) atTop (nhds 0) := by
  obtain ⟨hc,hi⟩ := information_entry_regular π hπ f g L K hf hg hfc hgc
  exact unbounded_stationary_time_average_L1 P π Y hY hcY hlaw T hT hlim _ hc hi

end Asakura.Chapter8

import Appendix
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
open Set Filter MeasureTheory
open scoped Topology
namespace Asakura

/-- C.2: extend good paths on a dense set, prove measurability at every time,
and prove the modification property using stochastic continuity. The event
and path extension are explicitly constructed, not postulated. -/
theorem continuous_modification_from_dense {T Ω : Type*}
    [MetricSpace T] [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (D : Set T) (hd : Dense D) (X : T → Ω → ℝ)
    (hm : ∀ t, Measurable (X t))
    (hstoch : ∀ t, TendstoInMeasure μ X (𝓝 t) (X t))
    (S : Set Ω) (hS : MeasurableSet S) (hSfull : ∀ᵐ ω ∂μ, ω ∈ S)
    (huc : ∀ ω ∈ S, UniformContinuous (fun t : D => X t ω)) :
    ∃ Y : T → Ω → ℝ,
      (∀ t, Measurable (Y t)) ∧
      (∀ ω, Continuous (fun t => Y t ω)) ∧
      (∀ t, Y t =ᵐ[μ] X t) ∧
      (∀ ω ∈ S, ∀ t : D, Y t ω = X t ω) ∧
      (∀ ω ∉ S, ∀ t, Y t ω = 0) := by
  classical
  let Y : T → Ω → ℝ := fun t ω => if ω ∈ S then
    hd.extend (fun s : D => X s ω) t else 0
  have hcont : ∀ ω, Continuous (fun t => Y t ω) := by
    intro ω
    by_cases hω : ω ∈ S
    · simpa only [Y, if_pos hω] using (hd.uniformContinuous_extend (huc ω hω)).continuous
    · simpa only [Y, if_neg hω] using (continuous_const : Continuous (fun _ : T => (0 : ℝ)))
  have hon : ∀ ω ∈ S, ∀ t : D, Y t ω = X t ω := by
    intro ω hω t
    simp only [Y, if_pos hω]
    exact hd.extend_of_ind (huc ω hω) t
  have hoff : ∀ ω ∉ S, ∀ t, Y t ω = 0 := by
    intro ω hω t
    simp only [Y, if_neg hω]
  have htime : ∀ t, Measurable (Y t) ∧ Y t =ᵐ[μ] X t := by
    intro t
    obtain ⟨a, haD, hat⟩ := mem_closure_iff_seq_limit.mp (hd t)
    let Z : ℕ → Ω → ℝ := fun n => S.indicator (X (a n))
    have hZm : ∀ n, Measurable (Z n) := fun n => (hm (a n)).indicator hS
    have hZlim : ∀ ω, Tendsto (fun n => Z n ω) atTop (𝓝 (Y t ω)) := by
      intro ω
      by_cases hω : ω ∈ S
      · have h := ((hcont ω).tendsto t).comp hat
        have heq : (fun n => Z n ω) = fun n => Y (a n) ω := by
          funext n
          simp only [Z, Set.indicator_of_mem hω]
          exact (hon ω hω ⟨a n, haD n⟩).symm
        rw [heq]
        exact h
      · simpa only [Z, Set.indicator_of_notMem hω, hoff ω hω t] using
          (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
    refine ⟨measurable_of_tendsto_metrizable hZm (tendsto_pi_nhds.mpr hZlim), ?_⟩
    have hXlim : ∀ᵐ ω ∂μ, Tendsto (fun n => X (a n) ω) atTop (𝓝 (Y t ω)) := by
      filter_upwards [hSfull] with ω hω
      simpa only [Z, Set.indicator_of_mem hω] using hZlim ω
    exact tendstoInMeasure_ae_unique
      (tendstoInMeasure_of_tendsto_ae (fun n => (hm (a n)).aestronglyMeasurable) hXlim)
      ((hstoch t).comp hat)
  exact ⟨Y, fun t => (htime t).1, hcont, fun t => (htime t).2, hon, hoff⟩

/-- Lp-continuity supplies the stochastic-continuity hypothesis of the construction. -/
theorem stochastic_continuity_of_lp {T Ω : Type*} [TopologicalSpace T]
    [MeasurableSpace Ω] (μ : Measure Ω) (X : T → Ω → ℝ)
    (p : ENNReal) (hp : p ≠ 0)
    (h : ∀ t, Tendsto (fun s => eLpNorm (X s - X t) p μ) (𝓝 t) (𝓝 0)) :
    ∀ t, TendstoInMeasure μ X (𝓝 t) (X t) :=
  fun t => tendstoInMeasure_of_tendsto_eLpNorm hp (h t)
end Asakura

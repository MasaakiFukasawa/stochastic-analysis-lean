import ContinuousModification
import DyadicContinuity
import SeriesBound
open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace Asakura

/-- C.2: complete continuous-modification construction from summable Lp grid
increments. The remaining cube-specific work is to supply the grid and its
moment estimate, not to assume a continuous modification. -/
theorem continuous_modification_of_dyadic_lp {T Ω : Type*}
    [MetricSpace T] [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (D : Set T) (hd : Dense D) (X : T → Ω → ℝ)
    (hm : ∀ t, Measurable (X t))
    (hstoch : ∀ t, TendstoInMeasure μ X (𝓝 t) (X t))
    (a : ℕ → D → D) (K : ℕ → Ω → ℝ)
    (hKm : ∀ n, Measurable (K n)) (hK0 : ∀ n ω, 0 ≤ K n ω)
    (p : ℝ≥0∞) (hp : 1 ≤ p)
    (hfinite : ∑' n, eLpNorm (K n) p μ ≠ ∞)
    (hfix : ∀ s, ∃ N, ∀ n ≥ N, a n s = s)
    (hstep : ∀ ω n s, dist (X (a (n+1) s) ω) (X (a n s) ω) ≤ K (n+1) ω)
    (hnear : ∀ ω m s t, dist s t ≤ (1/2 : ℝ)^m →
      dist (X (a m s) ω) (X (a m t) ω) ≤ K m ω) :
    ∃ Y : T → Ω → ℝ,
      (∀ t, Measurable (Y t)) ∧
      (∀ ω, Continuous (fun t => Y t ω)) ∧
      (∀ t, Y t =ᵐ[μ] X t) := by
  let S : Set Ω := {ω | Summable (fun n => K n ω)}
  have hSm : MeasurableSet S := measurable_summability_event K hKm
  have hSfull : ∀ᵐ ω ∂μ, ω ∈ S :=
    (nonnegative_series_lp_bound μ p hp K hKm hK0 hfinite).1
  have huc : ∀ ω ∈ S, UniformContinuous (fun t : D => X t ω) := by
    intro ω hω
    exact dyadic_uniform_continuity (fun t : D => X t ω) a (fun n => K n ω)
      (fun n => hK0 n ω) hω hfix (hstep ω) (hnear ω)
  obtain ⟨Y, hYm, hYc, hYX, _, _⟩ :=
    continuous_modification_from_dense μ D hd X hm hstoch S hSm hSfull huc
  exact ⟨Y, hYm, hYc, hYX⟩

/-- C.2: extend a Holder bound from the dense set to the whole parameter space. -/
theorem holder_bound_from_dense {T E : Type*} [MetricSpace T] [PseudoMetricSpace E]
    (D : Set T) (hd : Dense D) (f : T → E) (hf : Continuous f)
    (C α : ℝ) (ha : 0 ≤ α)
    (hD : ∀ s ∈ D, ∀ t ∈ D, dist (f s) (f t) ≤ C * (dist s t)^α) :
    ∀ s t, dist (f s) (f t) ≤ C * (dist s t)^α := by
  let A : Set (T × T) := {z | dist (f z.1) (f z.2) ≤ C * (dist z.1 z.2)^α}
  have hA : IsClosed A := isClosed_le
    ((hf.comp continuous_fst).dist (hf.comp continuous_snd))
    (continuous_const.mul ((continuous_fst.dist continuous_snd).rpow_const (fun _ => Or.inr ha)))
  have hsub : D ×ˢ D ⊆ A := fun z hz => hD z.1 hz.1 z.2 hz.2
  have hcl := hA.closure_subset_iff.mpr hsub
  rw [(hd.prod hd).closure_eq] at hcl
  exact fun s t => hcl (Set.mem_univ (s,t))

/-- The original increment-moment hypothesis supplies stochastic continuity. -/
theorem stochastic_continuity_of_power_bound {T Ω : Type*}
    [MetricSpace T] [MeasurableSpace Ω] (μ : Measure Ω) (X : T → Ω → ℝ)
    (p : ℝ≥0∞) (hp : p ≠ 0) (C β : ℝ) (hβ : 0 < β)
    (h : ∀ s t, eLpNorm (X s - X t) p μ ≤ ENNReal.ofReal (C * (dist s t)^β)) :
    ∀ t, TendstoInMeasure μ X (𝓝 t) (X t) := by
  apply stochastic_continuity_of_lp μ X p hp
  intro t
  have hc : Continuous (fun s : T => ENNReal.ofReal (C * (dist s t)^β)) :=
    ENNReal.continuous_ofReal.comp (continuous_const.mul
      ((continuous_id.dist continuous_const).rpow_const (fun _ => Or.inr hβ.le)))
  have ht : Tendsto (fun s : T => ENNReal.ofReal (C * (dist s t)^β)) (𝓝 t) (𝓝 0) := by
    simpa [Real.zero_rpow hβ.ne'] using hc.tendsto t
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
    (fun _ => bot_le) (fun s => h s t)
end Asakura

import KolmogorovConstruction
import DyadicHolder
open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace Asakura

/-- C.2: construction of a measurable Holder modification and an Lp-bounded
random Holder constant from the weighted grid series. -/
theorem holder_modification_of_dyadic_lp {T Ω : Type*}
    [MetricSpace T] [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (D : Set T) (hd : Dense D) (X : T → Ω → ℝ)
    (hm : ∀ t, Measurable (X t))
    (hstoch : ∀ t, TendstoInMeasure μ X (𝓝 t) (X t))
    (a : ℕ → D → D) (K : ℕ → Ω → ℝ)
    (hKm : ∀ n, Measurable (K n)) (hK0 : ∀ n ω, 0 ≤ K n ω)
    (p : ℝ≥0∞) (hp : 1 ≤ p) (α : ℝ) (hα : 0 < α)
    (hdiam : ∀ s t : D, dist s t ≤ 1)
    (hfinite : ∑' n, eLpNorm (fun ω => (2^α : ℝ)^n * K n ω) p μ ≠ ∞)
    (hfix : ∀ s, ∃ N, ∀ n ≥ N, a n s = s)
    (hstep : ∀ ω n s, dist (X (a (n+1) s) ω) (X (a n s) ω) ≤ K (n+1) ω)
    (hnear : ∀ ω m s t, dist s t ≤ (1/2 : ℝ)^m →
      dist (X (a m s) ω) (X (a m t) ω) ≤ K m ω) :
    ∃ (Y : T → Ω → ℝ) (M : Ω → ℝ),
      (∀ t, Measurable (Y t)) ∧ (∀ ω, Continuous (fun t => Y t ω)) ∧
      (∀ t, Y t =ᵐ[μ] X t) ∧ Measurable M ∧ (∀ ω, 0 ≤ M ω) ∧
      (∀ ω s t, dist (Y s ω) (Y t ω) ≤ M ω * (dist s t)^α) ∧
      eLpNorm M p μ ≤ ENNReal.ofReal (2 * 2^α) *
        ∑' n, eLpNorm (fun ω => (2^α : ℝ)^n * K n ω) p μ := by
  classical
  let f : ℕ → Ω → ℝ := fun n ω => (2^α : ℝ)^n * K n ω
  have hfm : ∀ n, Measurable (f n) := fun n => measurable_const.mul (hKm n)
  have hf0 : ∀ n ω, 0 ≤ f n ω := fun n ω => mul_nonneg (by positivity) (hK0 n ω)
  have hseries := nonnegative_series_lp_bound μ p hp f hfm hf0 hfinite
  let S : Set Ω := {ω | Summable (fun n => f n ω)}
  let M : Ω → ℝ := fun ω => (2 * 2^α) * ∑' n, f n ω
  have hMm : Measurable M := measurable_const.mul hseries.2.1
  have hM0 : ∀ ω, 0 ≤ M ω := fun ω =>
    mul_nonneg (by positivity) (tsum_nonneg (fun n => hf0 n ω))
  have hDholder : ∀ ω ∈ S, ∀ s t : D,
      dist (X s ω) (X t ω) ≤ M ω * (dist s t)^α := by
    intro ω hω
    exact dyadic_holder_bound (fun s : D => X s ω) a (fun n => K n ω) α hα
      hdiam (fun n => hK0 n ω) hω hfix (hstep ω) (hnear ω)
  have huc : ∀ ω ∈ S, UniformContinuous (fun s : D => X s ω) :=
    fun ω hω => positive_holder_uniformContinuous _ (M ω) α hα (hDholder ω hω)
  obtain ⟨Y, hYm, hYc, hYX, hon, hoff⟩ := continuous_modification_from_dense μ D hd X
    hm hstoch S (measurable_summability_event f hfm) hseries.1 huc
  refine ⟨Y, M, hYm, hYc, hYX, hMm, hM0, ?_, ?_⟩
  · intro ω
    by_cases hω : ω ∈ S
    · apply holder_bound_from_dense D hd (fun t => Y t ω) (hYc ω) (M ω) α hα.le
      intro s hs t ht
      rw [hon ω hω ⟨s,hs⟩, hon ω hω ⟨t,ht⟩]
      exact hDholder ω hω ⟨s,hs⟩ ⟨t,ht⟩
    · intro s t
      rw [hoff ω hω s, hoff ω hω t, dist_self]
      exact mul_nonneg (hM0 ω) (Real.rpow_nonneg dist_nonneg α)
  · have heq : M = (2 * 2^α : ℝ) • (fun ω => ∑' n, f n ω) := rfl
    rw [heq, eLpNorm_const_smul, Real.enorm_eq_ofReal_abs,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * 2^α)]
    exact mul_le_mul_of_nonneg_left hseries.2.2 (by positivity)
end Asakura

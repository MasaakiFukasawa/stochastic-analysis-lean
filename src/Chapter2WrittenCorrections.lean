import ManuscriptDominated
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.Monotone

/- Corrections to the actual Chapter 2 proof steps. The probabilistic stopping-time
and martingale bridges not present in a theorem's statement are not certified here. -/
open MeasureTheory Set Filter
open scoped Topology BigOperators
namespace Asakura.Chapter2Written

/-- The corrected hitting proof uses a minimum on a compact time interval. -/
theorem compact_distance_zero_iff {E : Type*} [MetricSpace E]
    {X : ℝ → E} {F : Set E} (hF : IsClosed F) (hne : F.Nonempty)
    {t : ℝ} (ht : 0 ≤ t) (hX : ContinuousOn X (Icc 0 t)) :
    sInf ((fun s => Metric.infDist (X s) F) '' Icc 0 t) = 0 ↔
      ∃ s ∈ Icc 0 t, X s ∈ F := by
  let d := fun s => Metric.infDist (X s) F
  have hd : ContinuousOn d (Icc 0 t) := (Metric.continuous_infDist_pt F).comp_continuousOn hX
  obtain ⟨s, hs, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr ht) hd
  have he : sInf (d '' Icc 0 t) = d s := by
    apply le_antisymm
    · exact csInf_le ⟨0, by rintro y ⟨u, hu, rfl⟩; exact Metric.infDist_nonneg⟩ ⟨s, hs, rfl⟩
    · apply le_csInf ((nonempty_Icc.mpr ht).image d)
      rintro y ⟨u, hu, rfl⟩
      exact hmin hu
  constructor
  · intro hz
    refine ⟨s, hs, (hF.mem_iff_infDist_zero hne).mpr ?_⟩
    exact he.symm.trans hz
  · rintro ⟨u, hu, hhit⟩
    rw [he]
    apply le_antisymm
    · exact (hmin hu).trans_eq (Metric.infDist_zero_of_mem hhit)
    · exact Metric.infDist_nonneg

/-- The infimum of nonempty closed hitting times is itself a hitting time. -/
theorem closed_hit_infimum_mem {E : Type*} [TopologicalSpace E]
    {X : ℝ → E} (hX : Continuous X) {F : Set E} (hF : IsClosed F)
    (hne : ({s : ℝ | 0 ≤ s} ∩ X ⁻¹' F).Nonempty) :
    0 ≤ sInf ({s : ℝ | 0 ≤ s} ∩ X ⁻¹' F) ∧
    X (sInf ({s : ℝ | 0 ≤ s} ∩ X ⁻¹' F)) ∈ F := by
  have hc : IsClosed ({s : ℝ | 0 ≤ s} ∩ X ⁻¹' F) := isClosed_Ici.inter (hF.preimage hX)
  exact hc.csInf_mem hne ⟨0, fun _ h => h.1⟩

/-- Each increment squared is bounded by its absolute value times the largest increment. -/
theorem variation_square_sum {ι : Type*} (J : Finset ι) (a : ι → ℝ)
    {δ k : ℝ} (hδ : 0 ≤ δ) (ha : ∀ j ∈ J, |a j| ≤ δ)
    (hv : ∑ j ∈ J, |a j| ≤ k) :
    ∑ j ∈ J, (a j)^2 ≤ δ*k := by
  calc
    _ = ∑ j ∈ J, |a j| * |a j| := by simp only [← pow_two, sq_abs]
    _ ≤ ∑ j ∈ J, δ * |a j| := Finset.sum_le_sum fun j hj =>
      mul_le_mul_of_nonneg_right (ha j hj) (abs_nonneg _)
    _ = δ*(∑ j ∈ J, |a j|) := (Finset.mul_sum _ _ _).symm
    _ ≤ δ*k := mul_le_mul_of_nonneg_left hv hδ

/-- The k² domination in the repaired localization follows from total variation alone. -/
theorem variation_square_sum_bounded {ι : Type*} (J : Finset ι) (a : ι → ℝ)
    {k : ℝ} (hk : 0 ≤ k) (hv : ∑ j ∈ J, |a j| ≤ k) :
    ∑ j ∈ J, (a j)^2 ≤ k^2 := by
  have ha : ∀ j ∈ J, |a j| ≤ k := by
    intro j hj
    exact (Finset.single_le_sum (fun i _ => abs_nonneg (a i)) hj).trans hv
  simpa [pow_two] using variation_square_sum J a hk ha hv

/-- The repaired DCT step, using the appendix's original dominated-convergence proof.
The measurable square sums, uniform variation bound, and pathwise vanishing mesh
increments are explicit inputs, not unproved conclusions hidden in the statement. -/
theorem variation_square_integrals_vanish {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Q δ : ℕ → Ω → ℝ) (k : ℝ)
    (hQ : ∀ n, Measurable (Q n))
    (hbound : ∀ n ω, 0 ≤ Q n ω ∧ Q n ω ≤ k^2)
    (hsmall : ∀ n ω, Q n ω ≤ δ n ω * k)
    (hδ : ∀ ω, Tendsto (fun n => δ n ω) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω, Q n ω ∂P) atTop (𝓝 0) := by
  have ht : ∀ ω, Tendsto (fun n => Q n ω) atTop (𝓝 0) := by
    intro ω
    apply squeeze_zero (fun n => (hbound n ω).1) (fun n => hsmall n ω)
    simpa using (hδ ω).mul_const k
  simpa using Asakura.manuscript_dominated_convergence P Q (fun _ => 0) (fun _ => k^2)
    hQ measurable_const measurable_const (integrable_const _)
    (fun n => Eventually.of_forall fun ω => by
      simpa [Real.norm_eq_abs, abs_of_nonneg (hbound n ω).1] using (hbound n ω).2)
    (Eventually.of_forall ht)

end Asakura.Chapter2Written

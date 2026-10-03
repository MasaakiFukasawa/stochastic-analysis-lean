import FullAuditHeatLine
import FullAuditSmoothCutoff

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal ContDiff
namespace Asakura.FullAudit

noncomputable def heatTestOfSmooth (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (hb : ∀ n : ℕ, ∃ C : ℝ, ∀ x, ‖iteratedDeriv n f x‖ ≤ C) : HeatTest where
  F n := iteratedDeriv n f
  C n := Classical.choose (hb n)
  continuous n := hf.continuous_iteratedDeriv n (by simp)
  derivative n x := by
    rw [iteratedDeriv_succ]
    exact (hf.differentiable_iteratedDeriv n (ENat.natCast_lt_of_coe_top_le_withTop le_rfl n) x).hasDerivAt
  bound n := Classical.choose_spec (hb n)

noncomputable def cutoffHeatTest (a b : ℝ) (hab : a < b) : HeatTest :=
  heatTestOfSmooth (cltCutoff a b) (cltCutoff_smooth a b hab) (fun n => by
    obtain ⟨C,_,hC⟩ := cltCutoff_all_derivatives_bounded a b hab n
    exact ⟨C,fun x => by simpa only [Real.norm_eq_abs] using hC x⟩)

theorem cutoffHeatTest_zero (a b : ℝ) (hab : a < b) : (cutoffHeatTest a b hab).F 0 = cltCutoff a b := by
  simp [cutoffHeatTest,heatTestOfSmooth]

theorem cltCutoff_values (a b : ℝ) (hab : a < b) :
    (∀ y, 0 ≤ cltCutoff a b y ∧ cltCutoff a b y ≤ 1) ∧
    (∀ y ≤ a, cltCutoff a b y = 1) ∧ (∀ y ≥ b, cltCutoff a b y = 0) := by
  have hb := cltCutoff_indicator_bounds a b
  have h0 : ∀ y, 0 ≤ cltCutoff a b y := by
    intro y
    have hi : (0:ℝ) ≤ (Iic a).indicator (fun _ => (1:ℝ)) y := by
      by_cases hy : y ∈ Iic a <;> simp [Set.indicator,hy]
    exact hi.trans (hb y hab).1
  have h1 : ∀ y, cltCutoff a b y ≤ 1 := by
    intro y
    have hi : (Iio b).indicator (fun _ => (1:ℝ)) y ≤ 1 := by
      by_cases hy : y ∈ Iio b <;> simp [Set.indicator,hy]
    exact (hb y hab).2.trans hi
  refine ⟨fun y => ⟨h0 y,h1 y⟩,?_,?_⟩
  · intro y hy
    have h := (hb y hab).1
    simp only [Set.indicator_of_mem (show y ∈ Iic a from hy),Pi.one_apply] at h
    exact le_antisymm (h1 y) h
  · intro y hy
    have h := (hb y hab).2
    rw [Set.indicator_of_notMem (show y ∉ Iio b from not_lt_of_ge hy)] at h
    exact le_antisymm h (h0 y)

/-- The exact smooth cutoffs converge pointwise away from the CDF endpoint. -/
theorem cltCutoff_tendsto (a b : ℕ → ℝ) (x : ℝ)
    (hab : ∀ n, a n < b n) (ha : Tendsto a atTop (𝓝 x)) (hb : Tendsto b atTop (𝓝 x))
    (y : ℝ) (hy : y ≠ x) :
    Tendsto (fun n => cltCutoff (a n) (b n) y) atTop
      (𝓝 ((Iic x).indicator (fun _ => (1:ℝ)) y)) := by
  rcases lt_or_gt_of_ne hy with hy|hy
  · have he : ∀ᶠ n in atTop, cltCutoff (a n) (b n) y = 1 := by
      filter_upwards [(tendsto_order.mp ha).1 y hy] with n hn
      exact (cltCutoff_values (a n) (b n) (hab n)).2.1 y hn.le
    have ht := tendsto_const_nhds.congr' (he.mono fun n hn => hn.symm)
    simpa only [Set.indicator_of_mem (show y ∈ Iic x from hy.le)] using ht
  · have he : ∀ᶠ n in atTop, cltCutoff (a n) (b n) y = 0 := by
      filter_upwards [(tendsto_order.mp hb).2 y hy] with n hn
      exact (cltCutoff_values (a n) (b n) (hab n)).2.2 y hn.le
    have ht := tendsto_const_nhds.congr' (he.mono fun n hn => hn.symm)
    simpa only [Set.indicator_of_notMem (show y ∉ Iic x from not_le_of_gt hy)] using ht

/-- Dominated convergence turns the cutoff approximation into the desired
probability at a non-atomic endpoint. -/
theorem cltCutoff_integral_tendsto (μ : Measure ℝ) [IsFiniteMeasure μ]
    (a b : ℕ → ℝ) (x : ℝ) (hnull : μ {x} = 0)
    (hab : ∀ n, a n < b n) (ha : Tendsto a atTop (𝓝 x)) (hb : Tendsto b atTop (𝓝 x)) :
    Tendsto (fun n => ∫ y, cltCutoff (a n) (b n) y ∂μ) atTop (𝓝 (μ.real (Iic x))) := by
  have h := tendsto_integral_of_dominated_convergence (μ := μ) (fun _ => (1:ℝ))
    (fun n => (cltCutoff_smooth (a n) (b n) (hab n)).continuous.aestronglyMeasurable)
    (integrable_const 1) (fun n => ae_of_all _ fun y => by
      rw [Real.norm_eq_abs,abs_of_nonneg ((cltCutoff_values (a n) (b n) (hab n)).1 y).1]
      exact ((cltCutoff_values (a n) (b n) (hab n)).1 y).2)
    (show ∀ᵐ y ∂μ, Tendsto (fun n => cltCutoff (a n) (b n) y) atTop
      (𝓝 ((Iic x).indicator (fun _ => (1:ℝ)) y)) from by
      have hne : ∀ᵐ y ∂μ, y ≠ x := by simpa only [ae_iff,not_not,Set.setOf_eq_eq_singleton] using hnull
      exact hne.mono fun y hy => cltCutoff_tendsto a b x hab ha hb y hy)
  simpa only [integral_indicator measurableSet_Iic,setIntegral_const,smul_eq_mul,mul_one] using h

end Asakura.FullAudit

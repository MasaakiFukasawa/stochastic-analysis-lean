import Chapter12BoundedLpConvergence

open MeasureTheory Filter
open scoped ENNReal Topology
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false

/-- The dominated-convergence step in the chain rule: bounded derivatives
converging pointwise may multiply an arbitrary Lp Hilbert-valued derivative. -/
theorem bounded_multiplier_Lp_limit {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (p : ℝ≥0∞) (hp : 1 ≤ p) (hpt : p ≠ ∞)
    (u : Ω → H) (hu : MemLp u p P)
    (a : ℕ → Ω → ℝ) (b : Ω → ℝ)
    (ha : ∀ n, AEStronglyMeasurable (a n) P) (hb : AEStronglyMeasurable b P)
    (C : ℝ) (hC : 0 ≤ C)
    (hab : ∀ n, ∀ᵐ w ∂P, |a n w| ≤ C) (hbb : ∀ᵐ w ∂P, |b w| ≤ C)
    (ht : ∀ᵐ w ∂P, Tendsto (fun n => a n w) atTop (𝓝 (b w))) :
    Tendsto (fun n => eLpNorm (fun w => (a n w) • u w - b w • u w) p P) atTop (𝓝 0) := by
  have hdom : MemLp (fun w => C • u w) p P := hu.const_smul C
  have hi : MemLp (fun w => b w • u w) p P := hdom.of_le (hb.smul hu.aestronglyMeasurable) (by
    filter_upwards [hbb] with w hw
    simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg hC]
    exact mul_le_mul_of_nonneg_right hw (norm_nonneg _))
  have hui : UnifIntegrable (fun n w => a n w • u w) p P :=
    (unifIntegrable_const hp hpt hdom).ae_mono
      (fun n => (ha n).smul hu.aestronglyMeasurable) (fun n => by
        filter_upwards [hab n] with w hw
        rw [← ofReal_norm,← ofReal_norm]
        apply ENNReal.ofReal_le_ofReal
        simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg hC]
        exact mul_le_mul_of_nonneg_right hw (norm_nonneg _))
  exact tendsto_Lp_finite_of_tendsto_ae hp hpt
    (fun n => (ha n).smul hu.aestronglyMeasurable) hi hui
    (ht.mono fun w hw => hw.smul tendsto_const_nhds)

end Asakura.Chapter12

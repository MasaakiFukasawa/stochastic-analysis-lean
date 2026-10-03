import Chapter2StochasticFubiniPrinted

open MeasureTheory Set
open scoped ENNReal
namespace Asakura.Chapter8
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

/-- Bounded kernels on finite parameter and energy measure spaces satisfy
the exact mixed-L1(L2) assumption of the printed stochastic Fubini theorem. -/
theorem bounded_fubini_mixed_condition {A S : Type*} [MeasurableSpace A] [MeasurableSpace S]
    (μ : Measure A) (ν : Measure S) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (H : A × S → ℝ) (hH : Measurable H) (C : ℝ) (hC : 0≤C)
    (hb : ∀ a,∀ᵐ s ∂ν,|H (a,s)|≤C) :
    (∫⁻ a,eLpNorm (fun s => H (a,s)) 2 ν ∂μ)<∞ := by
  have hnorm a : eLpNorm (fun s => H (a,s)) 2 ν≤eLpNorm (fun _ : S => C) 2 ν := by
    have ha : Measurable (fun s => H (a,s)) := hH.comp measurable_prodMk_left
    apply eLpNorm_mono_ae ha.aestronglyMeasurable
    simpa only [Real.norm_eq_abs,abs_of_nonneg hC] using hb a
  have hh := lintegral_mono (μ := μ) (fun a => hnorm a)
  refine hh.trans_lt ?_
  rw [lintegral_const]
  exact ENNReal.mul_lt_top (memLp_const C : MemLp (fun _ : S => C) 2 ν).eLpNorm_lt_top (measure_lt_top μ univ)
end Asakura.Chapter8

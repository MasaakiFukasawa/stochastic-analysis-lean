import Chapter6DensityL2Transfer
import Chapter4TransitionLipschitz

open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
namespace Asakura.Chapter6
set_option maxHeartbeats 2000000

theorem density_transfer_square_limit {Ω : Type*} [MeasurableSpace Ω]
    (P Q : Measure Ω) [IsProbabilityMeasure P] (d : Ω → ℝ≥0) (hd : Measurable d)
    (hQ : Q=P.withDensity (fun w => (d w:ℝ≥0∞)))
    (hd2 : MemLp (fun w => (d w:ℝ)) 2 P) (X : ℕ → Ω → ℝ)
    (hX : ∀ n,MemLp (X n) 2 P)
    (hl : Tendsto (fun n => ∫ w,(X n w)^2 ∂P) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ w,‖X n w‖ ∂Q) atTop (𝓝 0) := by
  have hb n : (∫ w,‖X n w‖ ∂Q)≤Real.sqrt (∫ w,(d w:ℝ)^2 ∂P)*Real.sqrt (∫ w,(X n w)^2 ∂P) := by
    rw [hQ,integral_withDensity_eq_integral_smul hd]
    change (∫ w,(d w:ℝ)*‖X n w‖ ∂P)≤_
    have hh := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := P) Real.HolderConjugate.two_two
      (f := fun w => (d w:ℝ)) (g := fun w => ‖X n w‖)
      (ae_of_all _ (fun w => (d w).coe_nonneg)) (ae_of_all _ (fun w => norm_nonneg _)) (by simpa using hd2) (by simpa using (hX n).norm)
    simpa only [smul_eq_mul,Real.rpow_two,Real.norm_eq_abs,sq_abs,Real.sqrt_eq_rpow] using hh
  have hs : Tendsto (fun n => Real.sqrt (∫ w,(X n w)^2 ∂P)) atTop (𝓝 0) := by
    simpa only [Real.sqrt_zero,Function.comp_def] using Real.continuous_sqrt.continuousAt.tendsto.comp hl
  exact squeeze_zero (fun _ => integral_nonneg (fun _ => norm_nonneg _)) hb
    (by simpa using hs.const_mul (Real.sqrt (∫ w,(d w:ℝ)^2 ∂P)))

end Asakura.Chapter6

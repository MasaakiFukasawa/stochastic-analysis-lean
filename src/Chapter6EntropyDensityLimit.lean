import Chapter6EntropyUniform

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter6
set_option maxHeartbeats 1800000

/-- Removing the localization preserves mean one because of the proved
entropy tail estimate, not merely by Fatou's inequality. -/
theorem entropy_localized_density_limit
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (D : ℕ → Ω → ℝ) (hm : ∀ n,Measurable (D n)) (hi : ∀ n,Integrable (D n) P)
    (hp : ∀ n,∀ᵐ w ∂P,0 ≤ D n w)
    (hei : ∀ n,Integrable (fun w => D n w*Real.log (D n w)) P)
    (C : ℝ) (hC : ∀ n,(∫ w,D n w*Real.log (D n w) ∂P) ≤ C)
    (hmean : ∀ n,(∫ w,D n w ∂P) = 1)
    (Z : Ω → ℝ) (hz : ∀ᵐ w ∂P,Tendsto (fun n => D n w) atTop (𝓝 (Z w))) :
    Integrable Z P ∧ (∫ w,Z w ∂P) = 1 := by
  have hui := entropy_bound_uniform_integrable P D hm hi hp hei C hC
  have hzi := hui.integrable_of_ae_tendsto hz
  have hl := tendsto_Lp_finite_of_tendsto_ae (by norm_num : (1:ℝ≥0∞) ≤ 1) (by norm_num)
    (fun n => (hm n).aestronglyMeasurable) (hui.memLp_of_ae_tendsto hz) hui.unifIntegrable hz
  have hli : Tendsto (fun n => ∫⁻ w,‖D n w-Z w‖ₑ ∂P) atTop (𝓝 0) := by
    simpa only [eLpNorm_one_eq_lintegral_enorm ((hi _).sub hzi).aestronglyMeasurable,Pi.sub_apply] using hl
  have hh := tendsto_integral_of_L1 Z hzi.aestronglyMeasurable (Eventually.of_forall hi) hli
  simp only [hmean] at hh
  exact ⟨hzi,tendsto_nhds_unique hh tendsto_const_nhds⟩

end Asakura.Chapter6

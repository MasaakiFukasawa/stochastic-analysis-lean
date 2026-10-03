import Chapter2EnergyNorm
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

/-- Dominated convergence in L2 under an actual square-integrable envelope. -/
theorem dominated_l2_ae_convergence
    {S : Type*} [MeasurableSpace S] (μ : Measure S)
    (f : ℕ → S → ℝ) (g : S → ℝ) (b : S → ℝ) (hbLp : MemLp b 2 μ)
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) (hg : AEStronglyMeasurable g μ)
    (hb : ∀ n, ∀ᵐ r ∂μ, ‖f n r‖ ≤ ‖b r‖) (hgb : ∀ᵐ r ∂μ, ‖g r‖ ≤ ‖b r‖)
    (hl : ∀ᵐ r ∂μ, Tendsto (fun n => f n r) atTop (𝓝 (g r))) :
    Tendsto (fun n => eLpNorm (f n-g) 2 μ) atTop (𝓝 0) := by
  have hm n : MemLp (f n) 2 μ := hbLp.of_le (hf n) (hb n)
  have hmg : MemLp g 2 μ := hbLp.of_le hg hgb
  have hbound n : ∀ᵐ r ∂μ, ‖(f n r-g r)^2‖ ≤ 4*‖b r‖^2 := by
    filter_upwards [hb n,hgb] with r hn hgω
    have ht := norm_sub_le (f n r) (g r)
    have hh := pow_le_pow_left₀ (norm_nonneg _) (show ‖f n r-g r‖ ≤ 2*‖b r‖ by linarith) 2
    simpa only [norm_pow,mul_pow,show (2:ℝ)^2 = 4 by norm_num] using hh
  have hsq n : AEStronglyMeasurable (fun r => (f n r-g r)^2) μ :=
    (continuous_pow 2).comp_aestronglyMeasurable ((hf n).sub hg)
  have hp := tendsto_integral_of_dominated_convergence (μ := μ) (fun r => 4*‖b r‖^2)
    hsq (((memLp_two_iff_integrable_sq hbLp.norm.aestronglyMeasurable).mp hbLp.norm).const_mul 4) hbound (f := fun _ => (0:ℝ))
    (hl.mono (fun r hr => by simpa only [sub_self,zero_pow (by norm_num : (2:ℕ) ≠ 0)] using (hr.sub_const (g r)).pow 2))
  simp only [integral_zero] at hp
  have he := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hp
  have hr := (ENNReal.continuous_rpow_const (y := 1/(2:ℝ))).continuousAt.tendsto.comp he
  simp only [Function.comp_def,ENNReal.ofReal_zero,ENNReal.zero_rpow_of_pos (by norm_num : (0:ℝ) < 1/2)] at hr
  have hnorm n := real_eLpNorm_two_energy μ (f n-g) ((hm n).sub hmg)
  simpa only [hnorm,Pi.sub_apply] using hr

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.dominated_l2_ae_convergence

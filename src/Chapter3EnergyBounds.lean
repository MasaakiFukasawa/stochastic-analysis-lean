import Chapter2EnergyNorm
import Chapter3OrthogonalSum

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false

/-- Squaring an L2 norm bound gives exactly the second-moment bound,
including zero energy. No division by a potentially zero norm is used. -/
theorem square_integral_le_of_l2_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (f : Ω → ℝ) (hf : MemLp f 2 P) (C : ℝ) (hC : 0 ≤ C)
    (hn : eLpNorm f 2 P ≤ ENNReal.ofReal C) :
    (∫ ω, f ω^2 ∂P) ≤ C^2 := by
  rw [real_eLpNorm_two_energy P f hf] at hn
  have hp := ENNReal.rpow_le_rpow hn (by norm_num : (0:ℝ) ≤ 2)
  rw [← ENNReal.rpow_mul] at hp
  norm_num only [one_div,inv_mul_cancel₀ (by norm_num : (2:ℝ) ≠ 0),
    ENNReal.rpow_one,ENNReal.rpow_two] at hp
  rw [← ENNReal.ofReal_pow hC] at hp
  exact (ENNReal.ofReal_le_ofReal_iff (sq_nonneg C)).mp hp

/-- The bounded weight K contributes K squared to the error energy. -/
theorem weighted_square_integral_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (A f : Ω → ℝ) (hA : MemLp A ∞ P) (hf : MemLp f 2 P)
    (K : ℝ) (hK : 0 ≤ K) (hb : ∀ᵐ ω ∂P, |A ω| ≤ K) :
    (∫ ω, (A ω*f ω)^2 ∂P) ≤ K^2 * ∫ ω, f ω^2 ∂P := by
  have hi := (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).mp hf
  have hAf : MemLp (fun ω => A ω*f ω) 2 P := hA.mul hf
  have hAi := (memLp_two_iff_integrable_sq hAf.aestronglyMeasurable).mp hAf
  rw [← integral_const_mul]
  apply integral_mono_ae hAi (hi.const_mul (K^2))
  filter_upwards [hb] with ω hω
  rw [mul_pow]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  nlinarith [sq_abs (A ω),mul_nonneg (sub_nonneg.mpr hω) (add_nonneg hK (abs_nonneg (A ω)))]

/-- The finite quantitative error estimate after orthogonality, before Doob.
The per-increment estimate is in the same sqrt-energy form as lem:adiff. -/
theorem orthogonal_weighted_error_energy
    {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι]
    (P : Measure Ω) (s : Finset ι) (A Y : ι → Ω → ℝ)
    (hA : ∀ i ∈ s, MemLp (A i) ∞ P) (hY : ∀ i ∈ s, MemLp (Y i) 2 P)
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      (∫ ω, (A i ω*Y i ω)*(A j ω*Y j ω) ∂P) = 0)
    (δ K : ℝ) (hδ : 0 ≤ δ) (hK : 0 ≤ K)
    (hb : ∀ i ∈ s, ∀ᵐ ω ∂P, |A i ω| ≤ K)
    (e : ι → ℝ) (he : ∀ i ∈ s, 0 ≤ e i)
    (hn : ∀ i ∈ s, eLpNorm (Y i) 2 P ≤ ENNReal.ofReal (2*δ*Real.sqrt (e i))) :
    (∫ ω, (∑ i ∈ s, A i ω*Y i ω)^2 ∂P) ≤
      4*δ^2*K^2*(∑ i ∈ s, e i) := by
  rw [orthogonal_sum_energy P s (fun i ω => A i ω*Y i ω) (fun i hi => (hA i hi).mul (hY i hi)) horth]
  calc
    _ ≤ ∑ i ∈ s, K^2*(4*δ^2*e i) := by
      apply Finset.sum_le_sum
      intro i hi
      apply (weighted_square_integral_bound P (A i) (Y i) (hA i hi) (hY i hi) K hK (hb i hi)).trans
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg K)
      have hh := square_integral_le_of_l2_bound P (Y i) (hY i hi) (2*δ*Real.sqrt (e i))
        (mul_nonneg (mul_nonneg (by norm_num) hδ) (Real.sqrt_nonneg _)) (hn i hi)
      have heq : (2*δ*Real.sqrt (e i))^2 = 4*δ^2*e i := by
        rw [mul_pow,mul_pow,Real.sq_sqrt (he i hi)]
        ring
      simpa only [heq] using hh
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.square_integral_le_of_l2_bound
#print axioms Asakura.Chapter3Complete.weighted_square_integral_bound
#print axioms Asakura.Chapter3Complete.orthogonal_weighted_error_energy

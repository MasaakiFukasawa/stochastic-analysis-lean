import Chapter2ClippedLp

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
set_option maxHeartbeats 800000

/-- Truncation errors are dominated by the untruncated function. -/
theorem truncation_error_bound (L x : ℝ) (hL : 0 ≤ L) :
    |max (-L) (min L x)-x| ≤ |x| := by
  by_cases hx : x ≤ -L
  · rw [min_eq_right (by linarith : x ≤ L),max_eq_left hx]
    rw [abs_of_nonneg (by linarith : 0 ≤ -L-x),abs_of_nonpos (by linarith : x ≤ 0)]
    linarith
  · by_cases hx' : L ≤ x
    · rw [min_eq_left hx',max_eq_right (by linarith : -L ≤ L)]
      rw [abs_of_nonpos (by linarith : L-x ≤ 0),abs_of_nonneg (by linarith : 0 ≤ x)]
      linarith
    · rw [min_eq_right (not_le.1 hx').le,max_eq_right (not_le.1 hx).le,sub_self,abs_zero]
      exact abs_nonneg _

/-- The last pathwise dominated-convergence step in the density proof.
No finiteness assumption on the measure is needed beyond the stated
integrability of this path. -/
theorem truncation_power_integral_limit
    {S : Type*} [MeasurableSpace S] (μ : Measure S) (H : S → ℝ)
    (hH : AEStronglyMeasurable H μ) (p : ℝ) (hp : 0 < p)
    (hi : Integrable (fun x => |H x| ^ p) μ) :
    Tendsto (fun n : ℕ => ∫ x, |max (-(n:ℝ)) (min (n:ℝ) (H x))-H x| ^ p ∂μ)
      atTop (𝓝 0) := by
  have hm (n : ℕ) : AEStronglyMeasurable
      (fun x => |max (-(n:ℝ)) (min (n:ℝ) (H x))-H x| ^ p) μ :=
    (Real.continuous_rpow_const hp.le).comp_aestronglyMeasurable
      (((continuous_const.max (continuous_const.min continuous_id)).comp_aestronglyMeasurable hH).sub hH).norm
  have hb (n : ℕ) : ∀ᵐ x ∂μ,
      ‖|max (-(n:ℝ)) (min (n:ℝ) (H x))-H x| ^ p‖ ≤ |H x| ^ p := by
    apply Filter.Eventually.of_forall
    intro x
    rw [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) p)]
    exact Real.rpow_le_rpow (abs_nonneg _) (truncation_error_bound n (H x) (Nat.cast_nonneg n)) hp.le
  have hl (x) : Tendsto (fun n : ℕ => |max (-(n:ℝ)) (min (n:ℝ) (H x))-H x| ^ p)
      atTop (𝓝 0) := by
    obtain ⟨N,hN⟩ := exists_nat_ge |H x|
    have he : (fun n : ℕ => |max (-(n:ℝ)) (min (n:ℝ) (H x))-H x| ^ p) =ᶠ[atTop] fun _ => (0:ℝ) := by
      filter_upwards [eventually_ge_atTop N] with n hn
      have hn' : |H x| ≤ (n:ℝ) := hN.trans (by exact_mod_cast hn)
      have hbounds := abs_le.1 hn'
      rw [min_eq_right hbounds.2,max_eq_right hbounds.1,sub_self,abs_zero,Real.zero_rpow hp.ne']
    exact tendsto_const_nhds.congr' he.symm
  have h := tendsto_integral_of_dominated_convergence (fun x => |H x| ^ p) hm hi hb
    (f := fun _ => (0:ℝ)) (.of_forall hl)
  simpa only [integral_zero] using h

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.truncation_error_bound
#print axioms Asakura.Chapter2Complete.truncation_power_integral_limit

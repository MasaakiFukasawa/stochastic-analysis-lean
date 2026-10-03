import Chapter2BoundedLpApproximation
import Chapter2AdaptedStepClipping

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
set_option maxHeartbeats 900000

/-- The complete analytic upgrade in the density proof: truncate L2
approximants to the bound of the target, then obtain every finite positive
Lp error limit from that same sequence. -/
theorem clipped_L2_approximation_all_exponents
    {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsFiniteMeasure μ]
    (H : S → ℝ) (J : ℕ → S → ℝ)
    (hH : AEStronglyMeasurable H μ) (hJ : ∀ n, AEStronglyMeasurable (J n) μ)
    (h2 : ∀ n, MemLp (fun x => J n x-H x) 2 μ)
    (L : ℝ) (hL : 0 ≤ L) (hb : ∀ᵐ x ∂μ, |H x| ≤ L)
    (hlim : Tendsto (fun n => ∫ x, (J n x-H x)^2 ∂μ) atTop (𝓝 0))
    (p : ℝ) (hp : 0 < p) :
    Tendsto (fun n => ∫ x, |max (-L) (min L (J n x))-H x| ^ p ∂μ) atTop (𝓝 0) := by
  let f := fun n x => max (-L) (min L (J n x))-H x
  have hm n : AEStronglyMeasurable (f n) μ :=
    ((continuous_const.max (continuous_const.min continuous_id)).comp_aestronglyMeasurable (hJ n)).sub hH
  have hb' n : ∀ᵐ x ∂μ, |f n x| ≤ 2*L :=
    hb.mono fun x hx => (clipped_error_bounds L (J n x) (H x) hL hx).2
  have hfi n : Integrable (fun x => f n x ^ 2) μ :=
    (memLp_two_iff_integrable_sq (hm n)).1
      (MemLp.of_bound (hm n) (2*L) (by simpa only [Real.norm_eq_abs] using hb' n))
  have hle n : (∫ x, f n x ^ 2 ∂μ) ≤ ∫ x, (J n x-H x)^2 ∂μ := by
    apply integral_mono_ae (hfi n) ((memLp_two_iff_integrable_sq ((hJ n).sub hH)).1 (h2 n))
    filter_upwards [hb] with x hx
    have h := (clipped_error_bounds L (J n x) (H x) hL hx).1
    change (max (-L) (min L (J n x))-H x)^2 ≤ (J n x-H x)^2
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).2 h
  have hfzero : Tendsto (fun n => ∫ x, f n x ^ 2 ∂μ) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun n => integral_nonneg fun x => sq_nonneg _) hle
  exact bounded_square_limit_all_exponents μ f hm (2*L) (by positivity) hb' hfzero p hp

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.clipped_L2_approximation_all_exponents

import Chapter6BoundedVectorCovariance
import Chapter6NovikovWritten

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter6
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

lemma bounded_vector_clock_upper
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) {noise : ℕ}
    (H : Fin noise → Ω × ℝ → ℝ) (hHm : ∀ i,Measurable (H i))
    (K : ℝ) (hK : 0 ≤ K) (hHb : ∀ i z,|H i z| ≤ K)
    (C : HalfClosedTime → Ω → ℝ)
    (R : ℝ) (hR : 0 ≤ R)
    (he : C (realTimeClamp R) =ᵐ[P] fun w => ∫ r in 0..R,∑ i,(H i (w,r))^2) :
    ∀ᵐ w ∂P,C (realTimeClamp R) w ≤ (noise:ℝ)*K^2*R := by
  filter_upwards [he] with w hw
  rw [hw]
  have hi i : IntervalIntegrable (fun r => (H i (w,r))^2) volume 0 R := by
    simpa only [pow_two,Function.comp_def] using bounded_product_time_integrable _ _
      ((hHm i).comp measurable_prodMk_left) ((hHm i).comp measurable_prodMk_left)
      K hK (fun r => hHb i (w,r)) (fun r => hHb i (w,r)) R hR
  have hsum : IntervalIntegrable (fun r => ∑ i,(H i (w,r))^2) volume 0 R := by
    convert IntervalIntegrable.sum Finset.univ (fun i _ => hi i) using 1
    ext r
    simp
  calc
    _ ≤ ∫ r in 0..R,(noise:ℝ)*K^2 := by
      apply intervalIntegral.integral_mono_on hR
        hsum intervalIntegrable_const
      intro r hr
      calc
        ∑ i,(H i (w,r))^2 ≤ ∑ _i : Fin noise,K^2 := by
          apply Finset.sum_le_sum
          intro i _
          exact sq_le_sq.mpr (by simpa only [abs_of_nonneg hK] using hHb i (w,r))
        _ = _ := by simp
    _ = _ := by simp [mul_comm,mul_left_comm,mul_assoc]

lemma exponential_integrable_of_upper_bound
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsFiniteMeasure P]
    (C : Ω → ℝ) (hm : Measurable C) (K γ : ℝ) (hγ : 0 ≤ γ)
    (hk : ∀ᵐ w ∂P,C w ≤ K) : Integrable (fun w => Real.exp (γ*C w)) P := by
  apply Integrable.of_bound (Real.continuous_exp.measurable.comp (measurable_const.mul hm)).aestronglyMeasurable
    (Real.exp (γ*K))
  filter_upwards [hk] with w hw
  change ‖Real.exp (γ*C w)‖ ≤ Real.exp (γ*K)
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hw hγ)

end Asakura.Chapter6

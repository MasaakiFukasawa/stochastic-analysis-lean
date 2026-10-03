import Chapter6StoppedGrowthPathBound
import Chapter6BrownianObservedPath
import Chapter2CommonTimeEquality
import Chapter8BrownianForcingPath

open MeasureTheory Set Filter Finset
open scoped Topology BigOperators NNReal
namespace Asakura.Chapter8
open Asakura.Chapter6 Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
open Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- The original Brownian path has a finite squared supremum under the
linear-growth changed measure, by the actual drift identity and Gronwall. -/
theorem changed_brownian_path_moment {Ω : Type*} [MeasurableSpace Ω]
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {d : ℕ} (B : BrownianSystem P d) (BQ : BrownianSystem Q d)
    (H : Fin d → Ω × ℝ → ℝ) (hHc : ∀ j w,Continuous (fun r => H j (w,r)))
    (R K : ℝ) (hR : 0≤R) (hK : 0≤K)
    (hHb : ∀ w r,r∈Icc 0 R → ‖WithLp.toLp 2 (fun j => H j (w,r))‖≤
      K*(1+‖WithLp.toLp 2 (fun j => B.W j (realTimeClamp r) w)‖))
    (hrep : ∀ j r,r∈Icc 0 R → BQ.W j (realTimeClamp r)=ᵐ[Q]
      fun w => B.W j (realTimeClamp r) w-∫ s in 0..r,H j (w,s)) :
    MemLp (brownianObservedPath P B (ContinuousLinearEquiv.refl ℝ _) 0 R hR) 2 Q := by
  haveI : Nonempty (Icc (0:ℝ) R) := ⟨⟨0,le_rfl,hR⟩⟩
  let X := brownianObservedPath P B (ContinuousLinearEquiv.refl ℝ _) 0 R hR
  have hXm : Measurable X := brownian_observed_path_measurable P B _ _ _ _
  have hWc j w : Continuous (fun r : ℝ => B.W j (realTimeClamp r) w) := by
    apply continuous_iff_continuousAt.mpr
    intro r
    exact ((B.martingale j).path P B.F w _ (half_real_time_finite r)).comp real_time_clamp_continuous.continuousAt
  have hQc j w : Continuous (fun r : ℝ => BQ.W j (realTimeClamp r) w) := by
    apply continuous_iff_continuousAt.mpr
    intro r
    exact ((BQ.martingale j).path Q BQ.F w _ (half_real_time_finite r)).comp real_time_clamp_continuous.continuousAt
  have hcommon j := continuous_process_common_time_equality Q
    (fun r : Icc (0:ℝ) R => BQ.W j (realTimeClamp r.val))
    (fun (r : Icc (0:ℝ) R) w => B.W j (realTimeClamp r.val) w-∫ s in 0..r.val,H j (w,s))
    (fun w => (hQc j w).comp continuous_subtype_val)
    (fun w => ((hWc j w).sub (intervalIntegral.differentiable_integral_of_continuous (hHc j w)).continuous).comp continuous_subtype_val)
    (fun r => hrep j r.val r.property)
  obtain ⟨G,hG,hGp,_,hGb⟩ := brownian_path_L2_envelope_bound Q BQ R hR
  let V := fun w => ((d:ℝ)*K*R+G w)*Real.exp (((d:ℝ)*K+1)*R)
  have hV : MemLp V 2 Q := ((memLp_const ((d:ℝ)*K*R) : MemLp (fun _ : Ω => (d:ℝ)*K*R) 2 Q).add hG).mul_const _
  apply hV.mono hXm.aestronglyMeasurable
  filter_upwards [ae_all_iff.mpr hcommon] with w hw
  have hVp : 0≤V w := mul_nonneg (add_nonneg (by positivity) (hGp w)) (Real.exp_pos _).le
  rw [Real.norm_eq_abs,abs_of_nonneg hVp]
  apply (ContinuousMap.norm_le (X w) hVp).mpr
  intro r
  have hh := stopped_vector_growth_path_bound
    (fun t j => B.W j (realTimeClamp t) w) (fun t j => BQ.W j (realTimeClamp t) w)
    (fun t j => H j (w,t)) R R K (G w) hR ⟨hR,le_rfl⟩ hK (hGp w)
    (continuous_pi (fun j => hWc j w)).continuousOn (continuous_pi (fun j => hHc j w)).continuousOn
    (hHb w) (hGb w) (fun t ht j => by
      have he := hw j ⟨t,ht⟩
      simp only [min_eq_right ht.2]
      linarith) r.val r.property
  change ‖0+(ContinuousLinearEquiv.refl ℝ (Fin d → ℝ)) (fun j => B.W j (realTimeClamp r.val) w)‖≤V w
  simp only [ContinuousLinearEquiv.refl_apply,zero_add]
  exact (pi_norm_le_iff_of_nonneg (norm_nonneg (WithLp.toLp 2 (fun j => B.W j (realTimeClamp r.val) w)))).mpr
    (fun j => PiLp.norm_apply_le (WithLp.toLp 2 (fun j => B.W j (realTimeClamp r.val) w)) j) |>.trans hh
end Asakura.Chapter8

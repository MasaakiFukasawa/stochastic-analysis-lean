import Chapter10L2DominatedLocalMartingale
import Chapter4BrownianFiniteMoment
import Chapter4ClockRegularity
import Chapter8DynkinFubini

open MeasureTheory Set Filter
open scoped ENNReal
namespace Asakura.Chapter10
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter8
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

/-- A finite L2 envelope of the continuous integrand gives a true M2
integral. This is the admissibility justification in the Kyle profit proof. -/
theorem continuous_brownian_integral_martingale {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : HalfClosedTime → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t Q,MeasurableSet[m] Q → P Q=0 → MeasurableSet[F t] Q)
    (B C H Z : HalfClosedTime → Ω → ℝ)
    (hB : LocalMProcessWitness P F B) (hC : LocalCovarianceWitness P F B B C)
    (hclock : ∀ w (r : ℝ),0≤r → (r:EReal)<⊤ → C (realTimeClamp r) w=r)
    (hHm : ∀ t,t<⊤ → Measurable[F t] (H t))
    (hHc : ∀ w t,t<⊤ → ContinuousAt (fun s => H s w) t)
    (hZ : LocalMProcessWitness P F Z)
    (hZI : ItoCovarianceFormula P F B (fun z => H (realTimeClamp z.2) z.1) Z)
    (T : ℝ) (hT : 0≤T) (K : Ω → ℝ) (hK : MemLp K 2 P)
    (hb : ∀ᵐ w ∂P,∀ r∈Icc 0 T,‖H (realTimeClamp r) w‖≤‖K w‖) :
    ContinuousMpWitness P F 2 (fun t w => Z (min (realTimeClamp T) t) w) := by
  have hHr w : Continuous (fun r : ℝ => H (realTimeClamp r) w) := by
    apply continuous_iff_continuousAt.mpr
    intro r
    exact (hHc w _ (half_real_time_finite _)).comp real_time_clamp_continuous.continuousAt
  have hHmr r : Measurable[m] (H (realTimeClamp r)) :=
    (hHm _ (half_real_time_finite _)).mono (hle _) le_rfl
  have hm : Measurable (fun z : Ω × ℝ => (H (realTimeClamp z.2) z.1)^2) :=
    ((measurable_uncurry_of_continuous_of_measurable hHr hHmr).comp measurable_swap).pow_const 2
  have hi := (dynkin_fubini P T hT (fun w r => (H (realTimeClamp r) w)^2) hm
    (fun w => (K w)^2) hK.integrable_sq (by
      filter_upwards [hb] with w hw
      intro r hr
      simpa only [Real.norm_eq_abs,abs_sq,sq_abs] using
        (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (hw r hr))).1
  obtain ⟨hCm,hCc⟩ := clock_regular_from_identity C hclock
  obtain ⟨hc,hM,_⟩ := brownian_ito_finite_path_moment P (by simp : (0:EReal)<⊤)
    F hF hle hnull B C H Z hB hC hCm hCc hclock hHm hHc hZ hZI T hT (EReal.coe_lt_top _) hi
  apply finite_l2_dominated_local_martingale P F hF hle Z hZ T hT
    (fun w => ‖finiteRealPath Z T hc w‖) hM.norm
  apply ae_of_all
  intro w t
  have hh := (finiteRealPath Z T hc w).norm_coe_le_norm (finitePrefixTime T hT t)
  change ‖Z (realTimeClamp (finitePrefixTime T hT t).val) w‖≤_ at hh
  rw [finite_prefix_time_clamp T hT le_top] at hh
  exact hh

end Asakura.Chapter10

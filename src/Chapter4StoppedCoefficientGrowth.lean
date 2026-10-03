import Chapter4FiniteMomentStops

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

/-- Stopping preserves the growth estimate, expressed in terms of the
stopped solution itself, with a constant independent of the level. -/
theorem stopped_coefficient_power_growth
    {Ω : Type*} {T : EReal} [Fact (0≤T)]
    (R : ℝ) (hR : 0≤R) (hRT : (R:EReal)<T)
    (Y Z : Ω → C(Icc (0:ℝ) R,ℝ)) (τ : Ω → ClosedTime T)
    (he : ∀ w r,Z w r=Y w (finitePrefixTime (T := T) R hR (min (τ w) (realTimeClamp r.val))))
    (b : ℝ → ℝ) (L : ℝ) (hL : 0≤L) (hgrowth : ∀ x,(b x)^2≤L*(1+x^2))
    (p : ℝ) (hp : 0<p) :
    ∀ w r,r∈Icc 0 R →
      |(Ioc (⊥ : ClosedTime T) (τ w)).indicator
        (fun _ => b (Y w (projIcc 0 R hR r))) (realTimeClamp r)|^p≤
        (L^(p/2)*(2:ℝ)^(p/2))*(1+|Z w (projIcc 0 R hR r)|^p) := by
  classical
  intro w r hr
  by_cases h : realTimeClamp (T := T) r∈Ioc (⊥ : ClosedTime T) (τ w)
  · rw [indicator_of_mem h,he]
    rw [projIcc_of_mem hR hr,min_eq_right h.2,finite_path_lift_real R hR hRT.le Y w r hr]
    rw [projIcc_of_mem hR hr]
    exact square_growth_power_bound _ _ L p hL hp.le (hgrowth _)
  · rw [indicator_of_notMem h,abs_zero,Real.zero_rpow hp.ne']
    exact mul_nonneg (mul_nonneg (Real.rpow_nonneg hL _) (Real.rpow_nonneg (by norm_num) _))
      (add_nonneg zero_le_one (Real.rpow_nonneg (abs_nonneg _) _))

/-- A bounded stopping time is measurable in the ambient sigma algebra. -/
lemma bounded_stopping_time_measurable
    {Ω : Type*} {m : MeasurableSpace Ω} {T : EReal} [Fact (0≤T)]
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (τ : Ω → ClosedTime T) (hτ : ∀ t,MeasurableSet[F t] {w | τ w≤t})
    (b : ClosedTime T) (hb : ∀ w,τ w≤b) : Measurable[m] τ := by
  have hh := (stopped_min_measurable F hF τ hτ b).mono (hle _) le_rfl
  simpa only [min_eq_left (hb _)] using hh

lemma stopped_integrand_joint_measurable
    {Ω : Type*} [MeasurableSpace Ω] {T : EReal} [Fact (0≤T)]
    (τ : Ω → ClosedTime T) (hτ : Measurable τ) (H : Ω × ℝ → ℝ) (hH : Measurable H) :
    Measurable (fun z : Ω × ℝ => (Ioc (⊥ : ClosedTime T) (τ z.1)).indicator
      (fun _ => H z) (realTimeClamp z.2)) := by
  classical
  have hc : Measurable (fun z : Ω × ℝ => realTimeClamp (T := T) z.2) :=
    real_time_clamp_continuous.measurable.comp measurable_snd
  have ht : Measurable (fun z : Ω × ℝ => τ z.1) := hτ.comp measurable_fst
  have hm : MeasurableSet {z : Ω × ℝ | (⊥ : ClosedTime T)<realTimeClamp z.2 ∧ realTimeClamp z.2≤τ z.1} :=
    (measurableSet_lt measurable_const hc).inter (measurableSet_le (measurable_subtype_coe.comp hc) (measurable_subtype_coe.comp ht))
  convert hH.indicator hm using 1
  funext z
  simp only [indicator_apply,mem_Ioc,mem_setOf_eq]

end Asakura.Chapter4

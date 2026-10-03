import Chapter4StoppedTimeIntegral
import Chapter4StoppedCoefficientGrowth

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

lemma stopped_finite_coefficient_growth
    {Ω : Type*} {T : EReal} [Fact (0≤T)]
    (R : ℝ) (hR : 0≤R) (hRT : (R:EReal)<T)
    (Y Z : Ω → C(Icc (0:ℝ) R,ℝ)) (τ : Ω → ClosedTime T)
    (he : ∀ w r,Z w r=Y w (finitePrefixTime (T := T) R hR (min (τ w) (realTimeClamp r.val))))
    (H : Ω × ℝ → ℝ) (p K : ℝ) (hp : 0<p) (hK : 0≤K)
    (hg : ∀ w r,r∈Icc 0 R → |H (w,r)|^p≤K*(1+|Y w (projIcc 0 R hR r)|^p)) :
    ∀ w r,r∈Icc 0 R →
      |(Ioc (⊥ : ClosedTime T) (τ w)).indicator (fun _ => H (w,r)) (realTimeClamp r)|^p≤
        K*(1+|Z w (projIcc 0 R hR r)|^p) := by
  classical
  intro w r hr
  by_cases h : realTimeClamp (T := T) r∈Ioc (⊥ : ClosedTime T) (τ w)
  · rw [indicator_of_mem h,he,projIcc_of_mem hR hr,min_eq_right h.2,
      finite_path_lift_real R hR hRT.le Y w r hr]
    exact hg w r hr
  · rw [indicator_of_notMem h,abs_zero,Real.zero_rpow hp.ne']
    exact mul_nonneg hK (add_nonneg zero_le_one (Real.rpow_nonneg (abs_nonneg _) _))

/-- Evaluating the original equation at the stopped time gives an equation
with stopped drift and the actual stopped Ito integral. -/
lemma stopped_finite_equation
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {T : EReal} [Fact (0≤T)]
    (R : ℝ) (hR : 0≤R) (hRT : (R:EReal)<T)
    (Y Z : Ω → C(Icc (0:ℝ) R,ℝ)) (τ : Ω → ClosedTime T)
    (hτ : ∀ w,τ w<⊤) (hτR : ∀ w,τ w≤realTimeClamp R)
    (he : ∀ w r,Z w r=Y w (finitePrefixTime (T := T) R hR (min (τ w) (realTimeClamp r.val))))
    (ξ : Ω → ℝ) (U : Ω × ℝ → ℝ) (N J : ClosedTime T → Ω → ℝ)
    (hrep : ∀ᵐ w ∂P,∀ r,Y w r=ξ w+(∫ s in 0..r.val,U (w,s))+N (realTimeClamp r.val) w)
    (hJ : ∀ᵐ w ∂P,∀ t,t<⊤ → J t w=N (min (τ w) t) w) :
    ∀ᵐ w ∂P,∀ r,Z w r=ξ w+
      (∫ s in 0..r.val,(Ioc (⊥ : ClosedTime T) (τ w)).indicator (fun _ => U (w,s)) (realTimeClamp s))+
      J (realTimeClamp r.val) w := by
  filter_upwards [hrep,hJ] with w hw hj
  intro r
  let v := min (τ w) (realTimeClamp (T := T) r.val)
  have hvR : v≤realTimeClamp (T := T) R := (min_le_left _ _).trans (hτR w)
  have hvc : realTimeClamp (T := T) (finitePrefixTime R hR v).val=v := by
    rw [finite_prefix_time_clamp R hR hRT.le,min_eq_right hvR]
  have hvreal : (finitePrefixTime R hR v).val=(v:EReal).toReal := by
    have ht := congrArg (fun t : ClosedTime T => (t:EReal).toReal) hvc
    rw [real_time_clamp_eq _ (finitePrefixTime R hR v).property.1
      ((EReal.coe_le_coe (finitePrefixTime R hR v).property.2).trans hRT.le),EReal.toReal_coe] at ht
    exact ht
  rw [he,hw,hvc,hj _ (real_time_below r.val r.property.1 ((EReal.coe_le_coe r.property.2).trans_lt hRT)),
    time_integral_stochastic_interval (τ w) (hτ w) r.val r.property.1
      ((EReal.coe_le_coe r.property.2).trans_lt hRT),hvreal]
  rfl

end Asakura.Chapter4

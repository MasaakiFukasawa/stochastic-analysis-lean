import Chapter5ProgressiveDriftVariation
import Chapter4ExponentialWeight
import Chapter4FinitePathLift

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter5
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false

/-- Construct the adapted primitive of a nonnegative continuous rate
and its discount factor as continuous finite-variation processes. -/
theorem nonnegative_discount_process
    {Ω : Type*} {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F)
    (K : ClosedTime T → Ω → ℝ)
    (hKa : ∀ t,t<⊤ → Measurable[F t] (K t))
    (hKc : ∀ w t,t<⊤ → ContinuousAt (fun s => K s w) t)
    (R : ℝ) (hR : 0≤R) (hRT : (R:EReal)<T)
    (hKpos : ∀ w r,r∈Icc 0 R → 0≤K (realTimeClamp r) w) :
    ∃ A : ClosedTime T → Ω → ℝ,
      AdaptedLocalVariationWitness F A ∧ (∀ w,Continuous (fun t => A t w)) ∧
      (∀ t w,A t w=∫ r in 0..(finitePrefixTime R hR t).val,K (realTimeClamp r) w) ∧
      (∀ w,Monotone (fun t => A t w)) ∧
      AdaptedLocalVariationWitness F (fun t w => Real.exp (-A t w)) ∧
      (∀ t w,0<Real.exp (-A t w) ∧ Real.exp (-A t w)≤1) := by
  let G := fun z : Ω × ℝ => K (realTimeClamp z.2) z.1
  have hGc w : ContinuousOn (fun r => G (w,r)) (Icc 0 R) := by
    intro r hr
    exact ((hKc w _ (real_time_below r hr.1 ((EReal.coe_le_coe hr.2).trans_lt hRT))).comp
      real_time_clamp_continuous.continuousAt).continuousWithinAt
  have hGp := continuous_adapted_real_progressive F hF G R hR
    (fun r hr => hKa _ (real_time_below r hr.1 ((EReal.coe_le_coe hr.2).trans_lt hRT))) hGc
  obtain ⟨A,hA,hAc,hAe⟩ := progressive_integrable_drift_variation hT F hF R hR hRT.le G hGp
    (fun w => ((hGc w).intervalIntegrable_of_Icc hR).1)
  have hi w a b (ha : a∈Icc 0 R) (hb : b∈Icc 0 R) :
      IntervalIntegrable (fun r => G (w,r)) volume a b :=
    ((hGc w).mono (uIcc_subset_Icc ha hb)).intervalIntegrable
  have hAm w : Monotone (fun t => A t w) := by
    intro s t hst
    change A s w≤A t w
    rw [hAe,hAe]
    let a := (finitePrefixTime (T:=T) R hR s).val
    let b := (finitePrefixTime (T:=T) R hR t).val
    have ha : a∈Icc 0 R := (finitePrefixTime R hR s).property
    have hb : b∈Icc 0 R := (finitePrefixTime R hR t).property
    have hab : a≤b := finite_prefix_time_mono R hR hst
    have hnon : 0≤∫ r in a..b,G (w,r) := intervalIntegral.integral_nonneg hab
      (fun r hr => hKpos w r ⟨ha.1.trans hr.1,hr.2.trans hb.2⟩)
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (hi w 0 a ⟨le_rfl,hR⟩ ha) (hi w a b ha hb)
    change (∫ r in 0..a,G (w,r))≤∫ r in 0..b,G (w,r)
    linarith
  have hD := exponential_adapted_variation hT F hF A hA.adapted
    (fun w => (hAm w).monotoneOn _) (fun w t _ => (hAc w).continuousAt) (-1)
  refine ⟨A,hA,hAc,hAe,hAm,?_,?_⟩
  · simpa only [neg_one_mul] using hD
  intro t w
  refine ⟨Real.exp_pos _,Real.exp_le_one_iff.mpr (neg_nonpos.mpr ?_)⟩
  rw [hAe]
  apply intervalIntegral.integral_nonneg (finitePrefixTime R hR t).property.1
  intro r hr
  exact hKpos w r ⟨hr.1,hr.2.trans (finitePrefixTime R hR t).property.2⟩

end Asakura.Chapter4

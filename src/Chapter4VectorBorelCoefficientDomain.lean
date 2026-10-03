import Chapter4VectorFiniteLift
import Chapter2ContinuousIntegrand

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter4.Vector
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

/-- Borel coefficients with quadratic growth belong to the Ito integrand
domain along every continuous adapted path, without any path moment assumption. -/
theorem finite_borel_coefficient_domain
    {Ω : Type*} {m : MeasurableSpace Ω} {T : EReal} [Fact (0≤T)] {dim : ℕ}
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F)
    (R : ℝ) (hR : 0≤R) (hRT : (R:EReal)<T)
    (Y : Ω → C(Icc (0:ℝ) R,Fin dim → ℝ)) (hm : Measurable[m] Y)
    (ha : ∀ r,Measurable[F (realTimeClamp r.val)] (fun w => Y w r))
    (b : (Fin dim → ℝ) → ℝ) (hb : Measurable b)
    (L : ℝ) (hL : 0≤L) (hg : ∀ x,(b x)^2≤L*(1+‖x‖^2)) :
    let H := fun z : Ω × ℝ => b (Y z.1 (finitePrefixTime (T := T) R hR (realTimeClamp z.2)))
    Measurable[m.prod inferInstance] H ∧
    (∀ c,0≤c → @Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) c => F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) c => H (z.1,z.2.val))) ∧
    (∀ c,0≤c → ∀ w,IntervalIntegrable (fun r => H (w,r)^2) volume 0 c) := by
  letI : MeasurableSpace Ω := m
  let U := fun t w => Y w (finitePrefixTime (T := T) R hR t)
  have hU := finite_path_lift_regular F hF R hR hRT.le Y ha
  have htime : Continuous (fun r : ℝ => finitePrefixTime (T := T) R hR (realTimeClamp r)) :=
    (finite_prefix_time_continuous R hR).comp real_time_clamp_continuous
  have heval : Measurable (fun z : Ω × ℝ => U (realTimeClamp z.2) z.1) :=
    continuous_eval.measurable.comp ((hm.comp measurable_fst).prodMk (htime.measurable.comp measurable_snd))
  have hHm := hb.comp heval
  refine ⟨hHm,?_,?_⟩
  · intro c hc
    letI : MeasurableSpace (Ω × Icc (0:ℝ) c) := progressiveSpace (fun t : Icc (0:ℝ) c => F (realTimeClamp t.val))
    apply hb.comp
    apply measurable_pi_iff.mpr
    intro i
    exact continuous_adapted_real_progressive F hF (fun z => U (realTimeClamp z.2) z.1 i) c hc
      (fun r _ => (measurable_pi_apply i).comp (hU.1 _))
      (fun w => (((continuous_apply i).comp (hU.2 w)).comp real_time_clamp_continuous).continuousOn)
  · intro c hc w
    have hme : Measurable (fun r => b (U (realTimeClamp r) w)^2) :=
      (hHm.comp (measurable_const.prodMk measurable_id)).pow_const 2
    have hbound r : |b (U (realTimeClamp r) w)^2|≤L*(1+‖Y w‖^2) := by
      rw [abs_of_nonneg (sq_nonneg _)]
      apply (hg _).trans
      apply mul_le_mul_of_nonneg_left _ hL
      apply add_le_add le_rfl
      exact pow_le_pow_left₀ (norm_nonneg _) (ContinuousMap.norm_coe_le_norm (Y w) _) 2
    constructor
    · exact (integrable_const (L*(1+‖Y w‖^2))).mono' hme.aestronglyMeasurable (.of_forall hbound)
    · change Integrable _ (volume.restrict (Ioc c 0))
      rw [Ioc_eq_empty_of_le hc,Measure.restrict_empty]
      exact integrable_zero_measure

end Asakura.Chapter4.Vector

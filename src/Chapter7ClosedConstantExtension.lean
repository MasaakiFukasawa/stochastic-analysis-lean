import Chapter7ClosedPrefixProjection
import Chapter7ClosedLocalBound
import Chapter2LocalZeroMeanCriterion
import Chapter2LocalQuadraticVariation

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false

/-- A local martingale continuous at a finite endpoint extends constantly
past it as a genuine half-line local martingale. No terminal integrability
assumption is added. -/
theorem closed_local_constant_extension
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (R : ℝ) [Fact (0 ≤ (R:EReal))]
    (F : ClosedTime (R:EReal) → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t,F t ≤ m)
    (X : ClosedTime (R:EReal) → Ω → ℝ) (hX : LocalMProcessWitness P F X)
    (ha : ∀ t,Measurable[F t] (X t)) (hc : ∀ w,Continuous (fun t => X t w)) :
    LocalMProcessWitness P (fun t => F (closedPrefixProjection R t))
      (fun t w => X (closedPrefixProjection R t) w) := by
  let p := closedPrefixProjection R
  let e := closedPrefixInclusion R
  let G := fun t => F (p t)
  let Y := fun t w => X (p t) w
  have hG : Monotone G := hF.comp (closed_prefix_projection_mono R)
  have hGl t : G t ≤ m := hle _
  have hYa t : Measurable[G t] (Y t) := ha _
  have hYc w : Continuous (fun t => Y t w) := (hc w).comp (closed_prefix_projection_continuous R)
  have hY0 : Y ⊥ =ᵐ[P] 0 := by
    simpa only [Y,p,closed_prefix_projection_bot] using hX.initial P F
  apply (local_iff_zero_bounded_stopped_means P (by simp : (0:EReal) < ⊤)
    G hG hGl Y hYa (fun w t _ => (hYc w).continuousAt) hY0).mpr
  intro σ hσ hσtop K hb
  let τ := fun w => p (σ w)
  have hτ t : MeasurableSet[F t] {w | τ w ≤ t} := by
    by_cases ht : t < ⊤
    · have he : {w | τ w ≤ t} = {w | σ w ≤ e t} := by
        ext w
        exact closed_prefix_projection_le_iff R (σ w) t ht
      rw [he]
      have hh := hσ (e t)
      change MeasurableSet[F (p (e t))] _ at hh
      have hp : p (e t) = t := closed_prefix_projection_inclusion R t
      rw [hp] at hh
      exact hh
    · have ht' : t = ⊤ := top_le_iff.mp (le_of_not_gt ht)
      subst t
      simp
  have hma t : Measurable[F t] (fun w => X (min (τ w) t) w) :=
    stopped_min_value_measurable F hF τ hτ X ha (fun w t => (hc w).continuousAt.continuousWithinAt) t
  have hbound : ∀ᵐ w ∂P,∀ t,‖X (min (τ w) t) w‖ ≤ K := by
    filter_upwards [hb] with w hw
    intro t
    have hh := hw (e t)
    simpa only [Y,τ,p,e,(closed_prefix_projection_mono R).map_min,closed_prefix_projection_inclusion] using hh
  have hM := closed_local_martingale_of_path_bound P F hle _ (hX.stopped P F hF hle τ hτ)
    hma (fun w => (hc w).comp (continuous_const.min continuous_id)) (fun _ => K) (memLp_const _) hbound
  have he := integral_congr_ae ((hM.martingale ⊥ ⊤ le_top).trans hM.initial)
  rw [integral_condExp (hle ⊥)] at he
  simpa only [min_top_right,Pi.zero_apply,integral_zero] using he

end Asakura.Chapter7

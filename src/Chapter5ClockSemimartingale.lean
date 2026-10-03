import Chapter5ConstructedMultivariateIto
import Chapter2FiniteTimeProjection

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete

theorem global_variation_localized {Ω : Type*} {T : EReal} [Fact (0 ≤ T)]
    (hT : 0 < T) (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F)
    (A : ClosedTime T → Ω → ℝ) (hA : AdaptedVariationWitness F A) :
    AdaptedLocalVariationWitness F A := by
  obtain ⟨u,_,_,_,hum,hut,huc⟩ := positive_real_time_exhaustion hT
  have hs n t : MeasurableSet[F t] {w : Ω | realTimeClamp (u n) ≤ t} := by
    by_cases h : realTimeClamp (T := T) (u n) ≤ t
    · simp only [h,ofPred_true]; exact .univ
    · simp only [h,ofPred_false]; exact @MeasurableSet.empty Ω (F t)
  exact ⟨fun n _ => realTimeClamp (u n),hs,(fun _ => hum.monotone),
    (fun n _ => hut n),(fun _ => huc),
    fun n => hA.stopped hF (fun _ => realTimeClamp (u n)) (hs n)⟩

/-- The deterministic time coordinate is constructed as a semimartingale,
with zero martingale part. It is clipped only beyond the finite interval
on which the eventual Ito identity will be used. -/
theorem clipped_clock_semimartingale {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F)
    (R : ℝ) (hR : 0 ≤ R) :
    SemimartingaleDecomposition P F
      (fun t _ => (finitePrefixTime (T := T) R hR t).val)
      (fun t _ => (finitePrefixTime (T := T) R hR t).val) (fun _ _ => 0) := by
  have hc : Continuous (fun t : ClosedTime T => (finitePrefixTime R hR t).val) :=
    continuous_subtype_val.comp (finite_prefix_time_continuous R hR)
  have hv : AdaptedVariationWitness F
      (fun t (_ : Ω) => (finitePrefixTime (T := T) R hR t).val) := by
    refine ⟨(fun t _ => (finitePrefixTime (T := T) R hR t).val),(fun _ _ => 0),?_,?_,?_,?_⟩
    · intro t; exact ⟨measurable_const,measurable_const⟩
    · intro w; exact ⟨fun s t hst => finite_prefix_time_mono R hR hst,monotone_const⟩
    · intro w t; exact ⟨hc.continuousAt.continuousWithinAt,continuousWithinAt_const⟩
    · intro t w; simp
  exact ⟨global_variation_localized hT F hF _ hv,zero_local_process P hT F,
    (fun _ _ _ => hc.continuousAt),(fun _ _ _ => by simp)⟩

end Asakura.Chapter5

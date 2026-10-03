import Chapter4FinitePathLift
import Chapter3BDGTwoMoments

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 1000000

lemma finite_real_path_norm_eq_runningMaximum
    {Ω : Type*} {T : EReal} [Fact (0≤T)]
    (X : ClosedTime T → Ω → ℝ)
    (hc : ∀ w t,t<⊤ → ContinuousAt (fun s => X s w) t)
    (R : ℝ) (hR : 0≤R) (hRT : (R:EReal)<T)
    (hs : ∀ w,Continuous (fun t => X (min (realTimeClamp R) t) w)) (w : Ω) :
    ‖finiteRealPath X R hs w‖=runningMaximum X hc (realTimeClamp R) w := by
  rw [runningMaximum_eq_path_norm X hc _ (real_time_below R hR hRT) hs w]
  apply le_antisymm (finite_real_path_norm_le X R hs w)
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).2
  intro t
  have h := ContinuousMap.norm_coe_le_norm (finiteRealPath X R hs w) (finitePrefixTime (T := T) R hR t)
  simpa only [continuousPath,finiteRealPath,ContinuousMap.coe_mk,finite_prefix_time_clamp R hR hRT.le] using h

end Asakura.Chapter4

import Chapter4FinitePathLift
import Chapter4VectorPaths

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter4.Vector
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
variable {dim : ℕ}
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

lemma finite_path_lift_regular
    {Ω : Type*} {T : EReal} [Fact (0≤T)]
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F)
    (R : ℝ) (hR : 0≤R) (hRT : (R:EReal)≤T)
    (Y : Ω → C(Icc (0:ℝ) R,Fin dim → ℝ))
    (hY : ∀ r,Measurable[F (realTimeClamp r.val)] (fun w => Y w r)) :
    (∀ t,Measurable[F t] (fun w => Y w (finitePrefixTime R hR t))) ∧
    (∀ w,Continuous (fun t => Y w (finitePrefixTime (T := T) R hR t))) := by
  constructor
  · intro t
    apply (hY _).mono (hF ?_) le_rfl
    rw [finite_prefix_time_clamp R hR hRT]
    exact min_le_right _ _
  · intro w
    exact (Y w).continuous.comp (finite_prefix_time_continuous R hR)

lemma finite_path_lift_real
    {Ω : Type*} {T : EReal} [Fact (0≤T)]
    (R : ℝ) (hR : 0≤R) (hRT : (R:EReal)≤T)
    (Y : Ω → C(Icc (0:ℝ) R,Fin dim → ℝ)) (w : Ω) (r : ℝ) (hr : r∈Icc 0 R) :
    Y w (finitePrefixTime (T := T) R hR (realTimeClamp r))=Y w (projIcc 0 R hR r) := by
  congr 1
  apply Subtype.ext
  rw [finite_prefix_time_of_real R r hR hr hRT]
  exact congrArg Subtype.val (projIcc_of_mem hR hr).symm

end Asakura.Chapter4.Vector

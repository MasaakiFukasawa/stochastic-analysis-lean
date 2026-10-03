import Chapter4PicardMapConstruction
import Chapter4FinitePathNorm

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

lemma real_time_below {T : EReal} [Fact (0≤T)] (r : ℝ) (hr : 0≤r) (hrt : (r:EReal)<T) :
    realTimeClamp (T := T) r<⊤ := by
  change (realTimeClamp r:EReal)<T
  rw [real_time_clamp_eq r hr hrt.le]
  exact hrt

lemma open_path_stopped_continuous {Ω : Type*} {T : EReal} [Fact (0≤T)]
    (X : ClosedTime T → Ω → ℝ)
    (hX : ∀ w t,t<⊤ → ContinuousAt (fun s => X s w) t)
    (R : ℝ) (hR : 0≤R) (hRT : (R:EReal)<T) :
    ∀ w,Continuous (fun t => X (min (realTimeClamp R) t) w) := by
  intro w
  apply continuous_iff_continuousAt.mpr
  intro t
  exact (hX w _ ((min_le_left _ _).trans_lt (real_time_below R hR hRT))).comp
    (continuous_const.min continuous_id).continuousAt

lemma finite_path_lift_regular
    {Ω : Type*} {T : EReal} [Fact (0≤T)]
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F)
    (R : ℝ) (hR : 0≤R) (hRT : (R:EReal)≤T)
    (Y : Ω → C(Icc (0:ℝ) R,ℝ))
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
    (Y : Ω → C(Icc (0:ℝ) R,ℝ)) (w : Ω) (r : ℝ) (hr : r∈Icc 0 R) :
    Y w (finitePrefixTime (T := T) R hR (realTimeClamp r))=Y w (projIcc 0 R hR r) := by
  congr 1
  apply Subtype.ext
  rw [finite_prefix_time_of_real R r hR hr hRT]
  exact congrArg Subtype.val (projIcc_of_mem hR hr).symm

end Asakura.Chapter4

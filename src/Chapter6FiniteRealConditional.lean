import Chapter6IntegrableIncrementConditional
import Chapter5BracketCommonTime
import Chapter7ClockHalfTime

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter6
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter7
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- Remove localizers on a finite real-time interval, starting with
fixed-time identities obtained by the stochastic calculus. -/
theorem finite_real_local_conditional {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : HalfClosedTime → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (X N : HalfClosedTime → Ω → ℝ) (hN : LocalMProcessWitness P F N)
    (ha : ∀ t,t<⊤ → Measurable[F t] (X t))
    (hc : ∀ w t,t<⊤ → ContinuousAt (fun s => X s w) t)
    (R : ℝ) (hR : 0≤R) (K : Ω → ℝ) (hK : Integrable K P)
    (hb : ∀ᵐ w ∂P,∀ r∈Icc 0 R,|X (realTimeClamp r) w|≤K w)
    (he : ∀ r∈Icc 0 R,X (realTimeClamp r)=ᵐ[P] fun w => X ⊥ w+N (realTimeClamp r) w)
    (s : ℝ) (hs : s∈Icc 0 R) :
    P[X (realTimeClamp R)|F (realTimeClamp s)]=ᵐ[P] X (realTimeClamp s) := by
  have hT : (0:EReal)<⊤ := by simp
  letI : Nonempty (Icc (0:ℝ) R) := ⟨⟨0,⟨le_rfl,hR⟩⟩⟩
  have hxc w : Continuous (fun r : Icc (0:ℝ) R => X (realTimeClamp r.val) w) :=
    continuousOn_iff_continuous_restrict.mp ((open_process_real_regularity F X ha hc).2 R hR (EReal.coe_lt_top R) w)
  have hnc w : Continuous (fun r : Icc (0:ℝ) R => N (realTimeClamp r.val) w) :=
    continuousOn_iff_continuous_restrict.mp ((open_process_real_regularity F N (hN.adapted P F) (hN.path P F)).2 R hR (EReal.coe_lt_top R) w)
  have hall := ae_continuous_common_time_equality P
    (fun r : Icc (0:ℝ) R => X (realTimeClamp r.val))
    (fun r : Icc (0:ℝ) R => fun w => X ⊥ w+N (realTimeClamp r.val) w)
    (ae_of_all _ hxc) (ae_of_all _ (fun w => continuous_const.add (hnc w))) (fun r => he r.val r.property)
  have hrep : ∀ t : HalfClosedTime,t≤realTimeClamp R → realTimeClamp (finitePrefixTime R hR t).val=t := by
    intro t ht
    rw [finite_prefix_time_clamp R hR le_top,min_eq_right ht]
  apply integrable_local_increment_conditional P hT F hF hle X N hN ha
    (realTimeClamp R) (changed_time_finite R hR) K hK _ _ (realTimeClamp s) (real_time_clamp_mono hs.2)
  · filter_upwards [hb] with w hw
    intro t ht
    simpa only [hrep t ht] using hw (finitePrefixTime R hR t).val (finitePrefixTime R hR t).property
  · filter_upwards [hall] with w hw
    intro t ht
    simpa only [hrep t ht] using hw (finitePrefixTime R hR t)

end Asakura.Chapter6

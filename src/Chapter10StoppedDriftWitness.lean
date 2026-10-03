import Chapter10StoppedDriftDensity
import Chapter10SDEDecomposition

open MeasureTheory Set Filter
namespace Asakura.Chapter10
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter9
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- The stopped prediction drift has the actual variation decomposition and
locally integrable density required by the reconstruction theorems. -/
theorem stopped_continuous_drift_witness {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : HalfClosedTime → MeasurableSpace Ω) (hF : Monotone F)
    (T : ℝ) (hT : 0≤T) (g : ℝ → Ω → ℝ)
    (hg : ∀ w,Continuous (fun s => g s w))
    (ha : ∀ s∈Icc 0 T,Measurable[F (realTimeClamp s)] (g s)) :
    let B := fun (t : HalfClosedTime) w => ∫ s in 0..(finitePrefixTime T hT t).val,g s w
    let b := fun s w => (Ioc (0:ℝ) T).indicator (fun s => g s w) s
    SemimartingaleDecomposition P F B B (fun _ _ => 0) ∧
      (∀ w,Measurable (fun s => b s w)) ∧
      (∀ w a d,IntervalIntegrable (fun s => b s w) volume a d) ∧
      ∀ w t,0≤t → B (realTimeClamp t) w=∫ s in 0..t,b s w := by
  intro B b
  have hb w := stopped_drift_density T hT (fun s => g s w) (hg w)
  have hBc w : Continuous (fun t => B t w) :=
    (intervalIntegral.continuous_primitive (fun a d => (hg w).intervalIntegrable a d) 0).comp
      (continuous_subtype_val.comp (finite_prefix_time_continuous T hT))
  refine ⟨⟨?_,zero_local_process P (by simp : (0:EReal)<⊤) F,
    fun w t _ => (hBc w).continuousAt,fun _ _ _ => by simp⟩,
    fun w => (hb w).1,fun w => (hb w).2.1,?_⟩
  · simpa only [zero_add] using continuous_drift_variation F hF g (fun _ => 0)
      measurable_const T hT ha (fun w => (hg w).continuousOn)
  · intro w t ht
    rw [(hb w).2.2 t ht]
    change (∫ s in 0..(finitePrefixTime (T := (⊤:EReal)) T hT (realTimeClamp t)).val,g s w)=_
    congr 1
    change (min (realTimeClamp (T := (⊤:EReal)) t : EReal) (T:EReal)).toReal=min T t
    rw [real_time_clamp_eq t ht le_top]
    rcases le_total t T with h | h
    · rw [min_eq_left (EReal.coe_le_coe h),EReal.toReal_coe,min_eq_right h]
    · rw [min_eq_right (EReal.coe_le_coe h),EReal.toReal_coe,min_eq_left h]

end Asakura.Chapter10

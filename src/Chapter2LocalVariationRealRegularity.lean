import Chapter2RealPathVariation

open MeasureTheory Set Filter
open scoped Topology ENNReal Classical
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem AdaptedLocalVariationWitness.real_interval_regular
    {Ω : Type*} {T : EReal} [Fact (0 ≤ T)]
    {F : ClosedTime T → MeasurableSpace Ω} {A : ClosedTime T → Ω → ℝ}
    (hA : AdaptedLocalVariationWitness F A)
    (d : ℝ) (hd : 0 ≤ d) (hdT : (d:EReal) < T) :
    (∀ ω r, r ∈ Icc 0 d → ContinuousWithinAt (fun s => A (realTimeClamp s) ω) (Icc 0 d ∩ Ici r) r) ∧
      (∀ r : Icc (0:ℝ) d, Measurable[F (realTimeClamp r.val)] (A (realTimeClamp r.val))) := by
  have hbelow r (hr : r ∈ Icc 0 d) : realTimeClamp (T := T) r < ⊤ := by
    change (realTimeClamp r : EReal) < T
    rw [real_time_clamp_eq r hr.1 ((EReal.coe_le_coe hr.2).trans hdT.le)]
    exact (EReal.coe_le_coe hr.2).trans_lt hdT
  constructor
  · intro ω r hr
    exact (hA.right_continuous ω _ (hbelow r hr)).comp
      real_time_clamp_continuous.continuousWithinAt (fun s hs => real_time_clamp_mono hs.2)
  · intro r
    exact hA.adapted (realTimeClamp r.val) (hbelow r.val r.property)

theorem finite_real_monotone_of_local
    {Ω : Type*} {T : EReal} [Fact (0 ≤ T)]
    (A : ClosedTime T → Ω → ℝ)
    (hm : ∀ ω, MonotoneOn (fun t => A t ω) (Iio ⊤))
    (d : ℝ) (hd : 0 ≤ d) (hdT : (d:EReal) < T) :
    ∀ ω, MonotoneOn (fun r => A (realTimeClamp r) ω) (Icc 0 d) := by
  have hbelow r (hr : r ∈ Icc 0 d) : realTimeClamp (T := T) r < ⊤ := by
    change (realTimeClamp r : EReal) < T
    rw [real_time_clamp_eq r hr.1 ((EReal.coe_le_coe hr.2).trans hdT.le)]
    exact (EReal.coe_le_coe hr.2).trans_lt hdT
  intro ω s hs t ht hst
  exact hm ω (hbelow s hs) (hbelow t ht) (real_time_clamp_mono hst)

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.AdaptedLocalVariationWitness.real_interval_regular

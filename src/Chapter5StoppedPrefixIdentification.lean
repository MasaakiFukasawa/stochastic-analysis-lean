import Chapter5StoppedIntegralFormula
import Chapter2ItoAssociativity

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

/-- A preterminal Ito formula uses the restriction of one common
integral whenever the derivative integrands agree up to the stopping time.
Values after the stopping time need not agree. -/
theorem stopped_integral_prefix_identification
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t N,MeasurableSet[m] N → P N=0 → MeasurableSet[F t] N)
    (X Y N : ClosedTime T → Ω → ℝ)
    (hX : LocalMProcessWitness P F X) (hY : LocalMProcessWitness P F Y) (hN : LocalMProcessWitness P F N)
    (H G : Ω × ℝ → ℝ)
    (hHm : ∀ w,Measurable (fun r => H (w,r))) (hGm : ∀ w,Measurable (fun r => G (w,r)))
    (a : ℝ) (ha : 0≤a)
    (hI : ItoCovarianceFormula P F (fun t w => X (min (realTimeClamp a) t) w) H N)
    (hYI : ItoCovarianceFormula P F X G Y)
    (he : ∀ w r,r∈Ioc 0 a → H (w,r)=G (w,r)) :
    ∀ᵐ w ∂P,∀ t,t<⊤ → N t w=Y (min (realTimeClamp a) t) w := by
  have hstop : ∀ t,MeasurableSet[F t] {w : Ω | realTimeClamp (T := T) a≤t} := by
    intro t
    by_cases h : realTimeClamp (T := T) a≤t <;> simp [h]
  have hXs := hX.stopped P F hF hle (fun _ => realTimeClamp a) hstop
  have hYs := hY.stopped P F hF hle (fun _ => realTimeClamp a) hstop
  have hst := stopped_ito_covariance_formula P hT F hF hle hnull X Y G hX hY hGm hYI a ha
  have hfun : (fun z : Ω × ℝ => H z*(Ioc 0 a).indicator (fun _ => (1:ℝ)) z.2)=
      (fun z => (Ioc 0 a).indicator (fun r => G (z.1,r)) z.2) := by
    funext z
    by_cases hz : z.2∈Ioc 0 a
    · simp only [indicator_of_mem hz,mul_one]
      exact he z.1 z.2 hz
    · simp only [indicator_of_notMem hz,mul_zero]
  apply ito_integral_associativity P hT F hF hle hnull X _ N _
    (fun z => (Ioc 0 a).indicator (fun _ => (1:ℝ)) z.2) H hX hXs hN hYs
    (fun _ => measurable_const.indicator measurableSet_Ioc) hHm
    (stopped_identity_ito_integral P hT F hF hle hnull X hX a ha) hI
  rw [hfun]
  exact hst

end Asakura.Chapter5

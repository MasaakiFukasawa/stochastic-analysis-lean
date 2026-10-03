import Chapter3ItoCompositionDecomposition
import Chapter7BrownianFutureProjection
import Chapter2StoppedRegularity

open MeasureTheory Set Filter Finset
open scoped Topology BigOperators
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

noncomputable def futureBrownianProjection {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (u : Fin d → ℝ) (s : ℝ) (t : HalfClosedTime) (w : Ω) : ℝ :=
    ∑ j,u j*(B.W j t w-B.W j (min (realTimeClamp s) t) w)

lemma future_brownian_process_regular {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (u : Fin d → ℝ) (s : ℝ) (hs : 0≤s) :
    (∀ t,t<⊤ → Measurable[B.F t] (futureBrownianProjection B u s t)) ∧
    (∀ w t,t<⊤ → ContinuousAt (fun r => futureBrownianProjection B u s r w) t) := by
  have hstop t : MeasurableSet[B.F t] {w : Ω | realTimeClamp s≤t} := by
    by_cases h : realTimeClamp s≤t <;> simp [h]
  have hr j := (B.martingale j).stopped_regular P B.F B.mono B.le
    (fun _ => realTimeClamp s) hstop (fun _ => real_time_below s hs (EReal.coe_lt_top _))
  constructor
  · intro t ht
    exact Finset.measurable_sum _ (fun j _ => measurable_const.mul
      (((B.martingale j).adapted P B.F t ht).sub ((hr j).1 t)))
  · intro w t ht
    exact finite_sum_continuousAt t Finset.univ _ (fun j _ => continuousAt_const.mul
      (((B.martingale j).path P B.F w t ht).sub (((hr j).2 w).continuousAt)))

lemma future_brownian_process_real {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (u : Fin d → ℝ) (s r : ℝ) (hr : 0≤r) (w : Ω) :
    futureBrownianProjection B u s (realTimeClamp r) w=
      ∑ j,u j*(B.W j (realTimeClamp (max 0 r)) w-B.W j (realTimeClamp (min s (max 0 r))) w) := by
  simp only [futureBrownianProjection,max_eq_right hr,real_time_clamp_mono.map_min]

end Asakura.Chapter7

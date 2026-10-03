import Chapter3ContinuousCommonBounds
import Chapter5IndependentAverage
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter5
open Asakura.Chapter3Complete

/-- Bounds on the terminal payoff hold for the continuous conditional
expectation simultaneously at every time, not just separately at each time. -/
theorem conditional_process_common_bounds
    {Ω D : Type*} [MeasurableSpace Ω]
    [TopologicalSpace D] [TopologicalSpace.SeparableSpace D] [Nonempty D]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : D → MeasurableSpace Ω) (hle : ∀ t,F t ≤ ‹MeasurableSpace Ω›)
    (U : Ω → ℝ) (hU : Integrable U P)
    (X : D → Ω → ℝ) (hX : ∀ w,Continuous (fun t => X t w))
    (hCE : ∀ t,X t =ᵐ[P] P[U|F t])
    (c B : ℝ) (hbound : ∀ᵐ w ∂P,c ≤ U w ∧ U w ≤ B) :
    ∀ᵐ w ∂P,∀ t,c ≤ X t w ∧ X t w ≤ B := by
  have ht t : ∀ᵐ w ∂P,0 ≤ X t w-c ∧ X t w-c ≤ B-c := by
    have hlo := condExp_mono (integrable_const c) hU (hbound.mono fun w hw => hw.1) (m := F t)
    have hhi := condExp_mono hU (integrable_const B) (hbound.mono fun w hw => hw.2) (m := F t)
    simp only [condExp_const (hle t)] at hlo hhi
    filter_upwards [hCE t,hlo,hhi] with w he hl hh
    rw [he]
    constructor <;> linarith
  have hh := continuous_process_common_bounds P
    (fun t w => X t w-c) (fun _ _ => B-c)
    (fun w => (hX w).sub continuous_const) (fun _ => continuous_const) ht
  filter_upwards [hh] with w hw
  intro t
  obtain ⟨h0,h1⟩ := hw t
  constructor <;> linarith

end Asakura.Chapter5

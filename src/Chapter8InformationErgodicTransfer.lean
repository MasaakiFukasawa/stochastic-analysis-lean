import Chapter8InformationObservable
import Chapter8InformationGrowth
import Chapter8InitialConditionTransfer
import Chapter8L1Transfer

open MeasureTheory Set Filter
open scoped Topology NNReal
namespace Asakura.Chapter8
open Asakura.FullAudit
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

/-- Complete the two approximation steps in the information limit:
spatial cutoffs under the stationary law, then synchronous coupling from
the prescribed deterministic initial condition. -/
theorem coupled_unbounded_time_average_probability {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (P : Measure Ω) [IsProbabilityMeasure P] (π : Measure E) [IsProbabilityMeasure π]
    (hπ : MemLp (fun x : E => x) 2 π)
    (X Y : Ω → ℝ → E) (hmX : Measurable (Function.uncurry X))
    (hmY : Measurable (Function.uncurry Y)) (hcX : ∀ w,Continuous (X w)) (hcY : ∀ w,Continuous (Y w))
    (hlaw : ∀ t,P.map (fun w => Y w t)=π)
    (x : E) (κ : ℝ) (hκ : 0<κ)
    (hXY : ∀ t≥0,∀ᵐ w ∂P,‖X w t-Y w t‖ ≤ Real.exp (-κ*t)*‖x-Y w 0‖)
    (T : ℕ → ℝ) (hT : ∀ n,0<T n) (hTlim : Tendsto T atTop atTop)
    (hlim : ∀ (g : E → ℝ) (L : ℝ≥0),LipschitzWith L g →
      (∃ K : ℝ,0 ≤ K ∧ ∀ z,|g z| ≤ K) →
      Tendsto (fun n => ∫ w,|timeAverage (fun t => g (Y w t)) (T n)-(∫ z,g z ∂π)| ∂P)
        atTop (nhds 0))
    (f : E → ℝ) (hf : ContDiff ℝ 1 f) (hi : Integrable f π)
    (C : ℝ) (hC : 0 ≤ C)
    (hLip : ∀ z z',|f z-f z'| ≤ C*‖z-z'‖*(1+‖z‖+‖z'‖)) :
    TendstoInMeasure P (fun n w => timeAverage (fun t => f (X w t)) (T n)) atTop
      (fun _ => ∫ z,f z ∂π) := by
  have hstat := unbounded_stationary_time_average_L1 P π Y hmY hcY hlaw T hT hlim f hf hi
  obtain ⟨D,hD,hr⟩ := initial_condition_time_average_bound P π hπ X Y hmX hmY hlaw x κ hκ hXY f hf.continuous C hC hLip
  let A := fun n w => timeAverage (fun t => f (X w t)) (T n)
  let B := fun n w => timeAverage (fun t => f (Y w t)) (T n)
  have he n w : timeAverage (fun t => f (X w t)-f (Y w t)) (T n)=A n w-B n w := by
    dsimp only [timeAverage,A,B]
    rw [intervalIntegral.integral_sub (f := fun t => f (X w t)) (g := fun t => f (Y w t))
      ((hf.continuous.comp (hcX w)).intervalIntegrable _ _)
      ((hf.continuous.comp (hcY w)).intervalIntegrable _ _)]
    ring
  have hRi n : Integrable (fun w => A n w-B n w) P := by
    simpa only [he] using (hr (T n) (hT n)).1
  have hBi n : Integrable (B n) P :=
    (stationary_time_average_L1_bound P π Y hmY hlaw f hf.continuous.measurable hi (T n) (hT n)).1
  have hRlim : Tendsto (fun n => ∫ w,|A n w-B n w| ∂P) atTop (nhds 0) := by
    have hh : Tendsto (fun n => (D/κ)/(T n)) atTop (nhds 0) := tendsto_const_nhds.div_atTop hTlim
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hh
      (fun n => integral_nonneg (fun _ => abs_nonneg _))
    intro n
    simpa only [he,div_mul_eq_div_div] using (hr (T n) (hT n)).2
  exact (l1_limit_transfer P atTop A B (∫ z,f z ∂π) hBi hRi hstat hRlim).2

end Asakura.Chapter8

import Chapter11ExponentialDecomposition
import Chapter11ExponentialDrift

open MeasureTheory Set Filter
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter6
set_option maxHeartbeats 4200000
set_option backward.isDefEq.respectTransparency false

/-- Exponential Ito supplies the exact decomposition and a common-event
 time-density identity, ready for the integrating-factor uniqueness proof. -/
theorem exponential_density_decomposition
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (X A N C : ClosedTime T → Ω → ℝ) (hX : SemimartingaleDecomposition P F X A N)
    (hC : LocalCovarianceWitness P F N N C)
    (c : ℕ → ℝ) (hc : ∀ n,0<c n) (hcm : Monotone c) (hcT : ∀ n,(c n:EReal)<T)
    (hcc : ∀ t,t<⊤ → ∃ n,t<realTimeClamp (T:=T) (c n))
    (b q : Ω × ℝ → ℝ) (hbm : ∀ w,Measurable (fun r => b (w,r)))
    (hqm : ∀ w,Measurable (fun r => q (w,r)))
    (hbi : ∀ n,∀ᵐ w ∂P,IntervalIntegrable (fun r => b (w,r)) volume 0 (c n))
    (hqi : ∀ n,∀ᵐ w ∂P,IntervalIntegrable (fun r => q (w,r)) volume 0 (c n))
    (hAe : ∀ n,∀ᵐ w ∂P,∀ r∈Icc 0 (c n),A (realTimeClamp r) w=A ⊥ w+∫ s in 0..r,b (w,s))
    (hCe : ∀ n,∀ᵐ w ∂P,∀ r∈Icc 0 (c n),C (realTimeClamp r) w=∫ s in 0..r,q (w,s)) :
    ∃ B M : ClosedTime T → Ω → ℝ,
      SemimartingaleDecomposition P F (fun t w => Real.exp (X t w)) B M ∧
      ItoCovarianceFormula P F N (fun z => Real.exp (X (realTimeClamp z.2) z.1)) M ∧
      (∀ n,∀ᵐ w ∂P,∀ r∈Icc 0 (c n),B (realTimeClamp r) w=B ⊥ w+
        ∫ s in 0..r,Real.exp (X (realTimeClamp s) w)*(b (w,s)+q (w,s)/2)) := by
  obtain ⟨B,M,I,J,hE,hMI,_,_,_⟩ := exponential_decomposition_constructed P hT F hF hle hnull
    X A N C hX hC c hc hcm hcT hcc
  refine ⟨B,M,hE,hMI,?_⟩
  intro n
  obtain ⟨L,hL,hLI,he⟩ := exponential_time_drift_constructed P hT F hF hle hnull X A N C hX hC
    b q hbm hqm (c n) (hc n).le (hcT n) (hbi n) (hqi n) (hAe n) (hCe n)
  have hLM := hLI.unique P hT F hF hle hnull N L M _ hX.martingale hL hE.martingale hMI
  have hBr w : ContinuousOn (fun r => B (realTimeClamp r) w-B ⊥ w) (Icc 0 (c n)) := by
    intro r hr
    exact (((hE.variation_continuous P F w _ (real_time_below r hr.1 ((EReal.coe_le_coe hr.2).trans_lt (hcT n)))).comp
      real_time_clamp_continuous.continuousAt).sub continuousAt_const).continuousWithinAt
  have hEr w : ContinuousOn (fun r => Real.exp (X (realTimeClamp r) w)) (Icc 0 (c n)) := by
    intro r hr
    exact (Real.continuous_exp.continuousAt.comp ((hX.continuous w _
      (real_time_below r hr.1 ((EReal.coe_le_coe hr.2).trans_lt (hcT n)))).comp
      real_time_clamp_continuous.continuousAt)).continuousWithinAt
  have hi : ∀ᵐ w ∂P,IntervalIntegrable (fun r => Real.exp (X (realTimeClamp r) w)*(b (w,r)+q (w,r)/2)) volume 0 (c n) := by
    filter_upwards [hbi n,hqi n] with w hb hq
    exact (hb.add (hq.div_const 2)).continuousOn_mul (by rw [uIcc_of_le (hc n).le];exact hEr w)
  have hh := bracket_primitive_common_time P (c n) (hc n).le
    (fun r w => B (realTimeClamp r) w-B ⊥ w)
    (fun w r => Real.exp (X (realTimeClamp r) w)*(b (w,r)+q (w,r)/2)) hBr hi (by
      intro r hr
      filter_upwards [he r hr,hLM,hE.martingale.initial P F] with w hew hl hm
      have hr' := real_time_below r hr.1 ((EReal.coe_le_coe hr.2).trans_lt (hcT n))
      rw [hl _ hr',hE.decomposition _ hr' w,hE.decomposition ⊥ hT w,hm] at hew
      simp only [Pi.zero_apply,add_zero] at hew
      linarith)
  filter_upwards [hh] with w hw
  intro r hr
  linarith [hw r hr]

end Asakura.Chapter11

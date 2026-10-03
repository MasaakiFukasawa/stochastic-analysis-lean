import Chapter13LocalDriftZero

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter13
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter11
set_option maxHeartbeats 3400000
set_option backward.isDefEq.respectTransparency false

/-- Actual Ito decomposition plus the local-martingale hypothesis forces the HJM exponent drift. -/
theorem exponential_martingale_drift_necessary
    {Ω:Type*} {m:MeasurableSpace Ω} (P:Measure Ω) [IsProbabilityMeasure P]
    {T:EReal} [Fact (0≤T)] (hT:0<T)
    (F:ClosedTime T → MeasurableSpace Ω) (hF:Monotone F) (hle:∀t,F t≤m)
    (hnull:∀t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (X A N C:ClosedTime T → Ω → ℝ) (hX:SemimartingaleDecomposition P F X A N)
    (hC:LocalCovarianceWitness P F N N C)
    (hE:LocalMProcessWitness P F (fun t w => Real.exp (X t w)-Real.exp (X ⊥ w)))
    (c:ℕ → ℝ) (hc:∀n,0<c n) (hcm:Monotone c) (hcT:∀n,(c n:EReal)<T)
    (hcc:∀t,t<⊤ → ∃n,t<realTimeClamp (T:=T) (c n))
    (b q:Ω × ℝ → ℝ) (hbm:∀w,Measurable (fun r => b (w,r)))
    (hqm:∀w,Measurable (fun r => q (w,r)))
    (hbi:∀n,∀ᵐw∂P,IntervalIntegrable (fun r => b (w,r)) volume 0 (c n))
    (hqi:∀n,∀ᵐw∂P,IntervalIntegrable (fun r => q (w,r)) volume 0 (c n))
    (hAe:∀n,∀ᵐw∂P,∀r∈Icc 0 (c n),A (realTimeClamp r) w=A ⊥ w+∫s in 0..r,b (w,s))
    (hCe:∀n,∀ᵐw∂P,∀r∈Icc 0 (c n),C (realTimeClamp r) w=∫s in 0..r,q (w,s)) :
    ∀n,∀ᵐw∂P,∀ᵐr∂volume,r∈Ioo 0 (c n) → b (w,r)=-q (w,r)/2 := by
  obtain ⟨D,M,hD,_,hDe⟩:=exponential_density_decomposition P hT F hF hle hnull
    X A N C hX hC c hc hcm hcT hcc b q hbm hqm hbi hqi hAe hCe
  have hz:=local_semimartingale_drift_constant P hT F hF hle _ D M hD hE
  intro n
  filter_upwards [hz,hDe n,hbi n,hqi n] with w hz he hb hq
  have hcont:ContinuousOn (fun r => Real.exp (X (realTimeClamp r) w)) (uIcc 0 (c n)) := by
    rw [uIcc_of_le (hc n).le]
    intro r hr
    exact (Real.continuous_exp.continuousAt.comp ((hX.continuous w _
      (real_time_below r hr.1 ((EReal.coe_le_coe hr.2).trans_lt (hcT n)))).comp
      real_time_clamp_continuous.continuousAt)).continuousWithinAt
  have hi:IntervalIntegrable (fun r => Real.exp (X (realTimeClamp r) w)*(b (w,r)+q (w,r)/2)) volume 0 (c n) :=
    (hb.add (hq.div_const 2)).continuousOn_mul hcont
  have hh:=zero_primitive_density_on _ (c n) (hc n).le hi (by
    intro r hr
    have hd:=he r hr
    rw [hz _ (real_time_below r hr.1 ((EReal.coe_le_coe hr.2).trans_lt (hcT n)))] at hd
    linarith)
  filter_upwards [hh] with r hr
  intro hri
  have h:=hr hri
  have hzero:= (mul_eq_zero.mp h).resolve_left (ne_of_gt (Real.exp_pos _))
  linarith
end Asakura.Chapter13
#print axioms Asakura.Chapter13.exponential_martingale_drift_necessary

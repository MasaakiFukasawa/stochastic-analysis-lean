import Chapter13HJMExponentialNecessity
import Chapter13HJMFinitePrimitive

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter13
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 3400000
set_option backward.isDefEq.respectTransparency false

/-- Assemble the HJM necessity argument from actual exponent decompositions.
Negative maturities can be filled with zero coefficients. The countable-event,
density, and differentiation steps are part of the conclusion's proof. -/
theorem hjm_drift_from_exponential_bonds
    {Ω:Type*} {m:MeasurableSpace Ω} (P:Measure Ω) [IsProbabilityMeasure P]
    {T:EReal} [Fact (0≤T)] (hT:0<T)
    (F:ClosedTime T → MeasurableSpace Ω) (hF:Monotone F) (hle:∀t,F t≤m)
    (hnull:∀t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (X A N C:ℚ → ClosedTime T → Ω → ℝ) (hX:∀u,SemimartingaleDecomposition P F (X u) (A u) (N u))
    (hC:∀u,LocalCovarianceWitness P F (N u) (N u) (C u))
    (hE:∀u,LocalMProcessWitness P F (fun t w => Real.exp (X u t w)-Real.exp (X u ⊥ w)))
    (c:ℕ → ℝ) (hc:∀n,0<c n) (hcm:Monotone c) (hcT:∀n,(c n:EReal)<T)
    (hcc:∀t,t<⊤ → ∃n,t<realTimeClamp (T:=T) (c n))
    {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (μ:Ω × ℝ → ℝ → ℝ) (σ:Ω × ℝ → ℝ → E)
    (hμ:∀z,LocallyIntegrable (μ z) volume) (hσ:∀z,LocallyIntegrable (σ z) volume)
    (hbm:∀u:ℚ,∀w,Measurable (fun r => -(∫s in 0..(u:ℝ),μ (w,r) s)))
    (hqm:∀u:ℚ,∀w,Measurable (fun r => ‖∫s in 0..(u:ℝ),σ (w,r) s‖^2))
    (hbi:∀u:ℚ,∀n,∀ᵐw∂P,IntervalIntegrable (fun r => -(∫s in 0..(u:ℝ),μ (w,r) s)) volume 0 (c n))
    (hqi:∀u:ℚ,∀n,∀ᵐw∂P,IntervalIntegrable (fun r => ‖∫s in 0..(u:ℝ),σ (w,r) s‖^2) volume 0 (c n))
    (hAe:∀u:ℚ,∀n,∀ᵐw∂P,∀r∈Icc 0 (c n),A u (realTimeClamp r) w=A u ⊥ w+∫v in 0..r,-(∫s in 0..(u:ℝ),μ (w,v) s))
    (hCe:∀u:ℚ,∀n,∀ᵐw∂P,∀r∈Icc 0 (c n),C u (realTimeClamp r) w=∫v in 0..r,‖∫s in 0..(u:ℝ),σ (w,v) s‖^2) :
    ∀n,∀ᵐw∂P,∀ᵐr∂volume,r∈Ioo 0 (c n) →
      (∀u:ℝ,∫s in 0..u,μ (w,r) s=‖∫s in 0..u,σ (w,r) s‖^2/2) ∧
      ∀ᵐu∂volume,μ (w,r) u=inner ℝ (σ (w,r) u) (∫s in 0..u,σ (w,r) s) := by
  have hu (u:ℚ):=exponential_martingale_drift_necessary P hT F hF hle hnull
    (X u) (A u) (N u) (C u) (hX u) (hC u) (hE u) c hc hcm hcT hcc
    (fun z => -(∫s in 0..(u:ℝ),μ z s)) (fun z => ‖∫s in 0..(u:ℝ),σ z s‖^2)
    (hbm u) (hqm u) (hbi u) (hqi u) (hAe u) (hCe u)
  intro n
  filter_upwards [ae_all_iff.mpr (fun u => hu u n)] with w hw
  filter_upwards [ae_all_iff.mpr hw] with r hr
  intro hri
  have hrat:∀u:ℚ,∫s in 0..(u:ℝ),μ (w,r) s=‖∫s in 0..(u:ℝ),σ (w,r) s‖^2/2 := by
    intro u
    have hh:=hr u hri
    linarith
  have hall:=hjm_primitive_from_dense (μ (w,r)) (σ (w,r)) (hμ (w,r)) (hσ (w,r)) hrat
  exact ⟨hall,hjm_drift_from_primitive (μ (w,r)) (σ (w,r)) (hμ (w,r)) (hσ (w,r)) hall⟩
end Asakura.Chapter13
#print axioms Asakura.Chapter13.hjm_drift_from_exponential_bonds

import EndToEndParameterItoConstructed
import EndToEndHJMOriginalForward

open MeasureTheory Set
namespace Asakura.EndToEnd
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter4
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

/-- The original HJM coefficient assumptions construct the parameterized
Ito integrals, their joint measurability, and the integrated drift restriction.
No stochastic-integral measurability or stochastic-Fubini identity is assumed. -/
theorem hjm_integrated_drift_constructed {Ω E:Type} {m:MeasurableSpace Ω} [MeasurableSpace E]
    (P:Measure Ω) [IsProbabilityMeasure P] {d:ℕ} (B:BrownianSystem P d)
    (μ:Measure E) [IsFiniteMeasure μ] (f0:E → ℝ) (hf0:Integrable f0 μ)
    (a:E × (Ω × ℝ) → ℝ) (σ:Fin d → E × (Ω × ℝ) → ℝ)
    (ham:Measurable a) (hσm:∀i,Measurable (σ i))
    (hap:∀b,0<b → @Measurable _ _
      ((inferInstance : MeasurableSpace E).prod (progressiveSpace (fun t:Icc (0:ℝ) b => B.F (realTimeClamp t.val)))) inferInstance
      (fun z:E × (Ω × Icc (0:ℝ) b) => a (z.1,(z.2.1,z.2.2.val))))
    (hσp:∀i b,0<b → @Measurable _ _
      ((inferInstance : MeasurableSpace E).prod (progressiveSpace (fun t:Icc (0:ℝ) b => B.F (realTimeClamp t.val)))) inferInstance
      (fun z:E × (Ω × Icc (0:ℝ) b) => σ i (z.1,(z.2.1,z.2.2.val))))
    (hab:∀w b,0≤b → ∃K:ℝ,0≤K ∧ ∀x r,r∈Icc 0 b → |a (x,(w,r))|≤K)
    (hσb:∀i w b,0≤b → ∃K:ℝ,0≤K ∧ ∀x r,r∈Icc 0 b → |σ i (x,(w,r))|≤K) :
    ∃ N : Fin d → E → HalfClosedTime → Ω → ℝ,
      (∀ i,Measurable (fun z : E × (Ω × HalfClosedTime) => N i z.1 z.2.2 z.2.1)) ∧
      (∀ i x,LocalMProcessWitness P B.F (N i x)) ∧
      (∀ i,∀ᵐ x ∂μ,ItoCovarianceFormula P B.F (B.W i) (fun z => -σ i (x,z)) (N i x)) ∧
      (let Price := fun (t : HalfClosedTime) w => Real.exp (-(∫x,f0 x+
        (∫s in 0..(t:EReal).toReal,a (x,(w,s)))-∑i,N i x t w∂μ))
       LocalMProcessWitness P B.F (fun t w => Price t w-Price ⊥ w) →
         ∀ R,0≤R → ∀ᵐ w ∂P,∀ᵐ r ∂volume,r∈Ioo 0 R →
           (∫x,a (x,(w,r))∂μ)=(∑i,(∫x,σ i (x,(w,r))∂μ)^2)/2) := by
  have hex i := parameter_ito_constructed P B i μ (fun z => -σ i z)
    (hσm i).neg (fun b hb => (hσp i b hb).neg)
    (fun w b hb => by simpa only [abs_neg] using hσb i w b hb)
  choose N hNm hN hNI using hex
  refine ⟨N,hNm,hN,hNI,?_⟩
  exact hjm_drift_from_forward_integrals_ae P B μ f0 hf0 a σ ham hσm hap hσp hab hσb N hN hNI hNm

#print axioms hjm_integrated_drift_constructed
end Asakura.EndToEnd

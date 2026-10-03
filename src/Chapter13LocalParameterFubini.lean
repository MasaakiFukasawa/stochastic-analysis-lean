import Chapter13StoppedField
import Chapter13StoppedParameterFubini

open MeasureTheory Set
namespace Asakura.Chapter13
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter4
set_option maxHeartbeats 3400000
set_option backward.isDefEq.respectTransparency false

/-- HJM stochastic Fubini localized directly from the manuscript's original
joint progressive field and its pathwise bound on a finite rectangle. -/
theorem local_parameter_fubini {Ω E:Type} {m:MeasurableSpace Ω} [MeasurableSpace E]
    (P:Measure Ω) [IsProbabilityMeasure P] {d:ℕ} (B:BrownianSystem P d) (i:Fin d)
    (μ:Measure E) [IsFiniteMeasure μ] (R:ℝ) (hR:0<R)
    (H:E × (Ω × ℝ) → ℝ) (hm:Measurable H)
    (hp:∀b,0<b → @Measurable _ _
      ((inferInstance : MeasurableSpace E).prod (progressiveSpace (fun t:Icc (0:ℝ) b => B.F (realTimeClamp t.val)))) inferInstance
      (fun z:E × (Ω × Icc (0:ℝ) b) => H (z.1,(z.2.1,z.2.2.val))))
    (hb:∀w,∃K:ℝ,0≤K ∧ ∀x r,r∈Icc 0 R → |H (x,(w,r))|≤K) :
    ∃τ:ℕ → Ω → HalfClosedTime,
      (∀n t,MeasurableSet[B.F t] {w | τ n w≤t}) ∧
      (∀w,∃N:ℕ,∀n,N≤n → τ n w=⊤) ∧
      ∀n,
        let K := fun z:E × (Ω × ℝ) =>
          (Ioc (0:ℝ) (finitePrefixTime R hR.le (τ n z.2.1)).val).indicator (fun r => H (z.1,(z.2.1,r))) z.2.2
        ∃Z:E → continuousM2Terminal P B.F,Integrable Z μ ∧
          (∀ᵐx∂μ,∃Y:HalfClosedTime → Ω → ℝ,∃hY:ContinuousM2Witness P B.F Y,
            ItoCovarianceFormula P B.F (B.W i) (fun z => K (x,z)) Y ∧ Z x=m2TerminalOfProcess P B.F Y hY) ∧
          ∃Ybar:HalfClosedTime → Ω → ℝ,∃hYbar:ContinuousM2Witness P B.F Ybar,
            ItoCovarianceFormula P B.F (B.W i) (fun z => ∫x,K (x,z)∂μ) Ybar ∧
            (∫x,Z x∂μ)=m2TerminalOfProcess P B.F Ybar hYbar := by
  obtain ⟨τ,hτ,htop,hen⟩:=localized_parameter_energy B.F B.mono μ R hR.le H hm (hp R hR) hb
  refine ⟨τ,hτ,htop,?_⟩
  intro n K
  obtain ⟨hKm,hKp⟩:=stopped_field_measurable B.F B.mono B.le R hR.le (τ n) (hτ n) H hm hp
  exact brownian_fubini_from_stopped_energy P B i μ K hKm hKp
    (ae_of_all _ fun w => (hen n w).1) ((n:ℝ)+1) (ae_of_all _ fun w => (hen n w).2)
end Asakura.Chapter13
#print axioms Asakura.Chapter13.local_parameter_fubini

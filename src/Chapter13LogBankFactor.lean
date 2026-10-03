import Chapter13PositiveLogDecomposition

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter13
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

/-- Multiplication by the bank account changes only the finite-variation
part of the logarithmic price. -/
theorem log_bank_factor_decomposition {Ω:Type*} {m:MeasurableSpace Ω}
    (P:Measure Ω) [IsProbabilityMeasure P] {T:EReal} [Fact (0≤T)] (hT:0<T)
    (F:ClosedTime T → MeasurableSpace Ω) (hF:Monotone F)
    (N V L A:ClosedTime T → Ω → ℝ)
    (hlog:SemimartingaleDecomposition P F (fun t w => Real.log (N t w)) V L)
    (hN:∀t w,0<N t w) (hA:AdaptedLocalVariationWitness F A)
    (hAc:∀w t,t<⊤ → ContinuousAt (fun s => A s w) t)
    (c:ℝ) (hc:0<c) :
    SemimartingaleDecomposition P F (fun t w => Real.log (c*Real.exp (A t w)*N t w))
      (fun t w => Real.log c+A t w+V t w) L := by
  have he t w:Real.log (c*Real.exp (A t w)*N t w)=Real.log c+A t w+Real.log (N t w) := by
    rw [Real.log_mul (mul_ne_zero hc.ne' (Real.exp_ne_zero _)) (hN t w).ne',Real.log_mul hc.ne' (Real.exp_ne_zero _),Real.log_exp]
  have hconst:=continuous_increasing_adapted_variation hT F hF (fun _ _ => Real.log c)
    (fun _ _ => measurable_const) (fun _ => monotoneOn_const) (fun _ _ _ => continuousAt_const)
  refine ⟨(hconst.add hA hF).add hlog.variation hF,hlog.martingale,?_,?_⟩
  · intro w t ht
    simp_rw [he]
    exact (continuousAt_const.add (hAc w t ht)).add (hlog.continuous w t ht)
  · intro t ht w
    rw [he,hlog.decomposition t ht w]
    ring
end Asakura.Chapter13
#print axioms Asakura.Chapter13.log_bank_factor_decomposition

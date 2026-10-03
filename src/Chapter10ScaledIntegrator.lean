import Chapter2ItoAssociativity
import Chapter4FiniteItoSum

open MeasureTheory Set Filter
namespace Asakura.Chapter10
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

/-- Constant scaling of the driving process is justified by actual Ito
associativity and covariance characterization. -/
theorem scaled_integrator_identity {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (B J Z : ClosedTime T → Ω → ℝ) (H : Ω × ℝ → ℝ) (a : ℝ)
    (hB : LocalMProcessWitness P F B) (hJ : LocalMProcessWitness P F J)
    (hZ : LocalMProcessWitness P F Z) (hHm : ∀ w,Measurable (fun s => H (w,s)))
    (hJI : ItoCovarianceFormula P F (fun t w => a*B t w) H J)
    (hZI : ItoCovarianceFormula P F B H Z) :
    ∀ᵐ w ∂P,∀ t,t<⊤ → J t w=a*Z t w := by
  have hzero := constant_ito_integral P hT F hF hle hnull B hB 0
  have hscaled : ItoCovarianceFormula P F B (fun z => H z*a) (fun t w => a*Z t w) := by
    have hh := hZI.add_smul P F hF hle B Z (fun t w => 0*B t w) H (fun _ => 0) hzero a
    simpa only [mul_zero,zero_mul,add_zero,mul_comm a] using hh
  exact ito_integral_associativity P hT F hF hle hnull B (fun t w => a*B t w) J
    (fun t w => a*Z t w) (fun _ => a) H hB (hB.smul P F a) hJ (hZ.smul P F a)
    (fun _ => measurable_const) hHm (constant_ito_integral P hT F hF hle hnull B hB a) hJI hscaled

end Asakura.Chapter10

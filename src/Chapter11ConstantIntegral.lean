import Chapter3IdentityItoIntegral
import Chapter2ItoCovarianceCharacterization

open MeasureTheory Set Filter
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- Identify the actual integral of a constant with the scaled integrator. -/
theorem constant_ito_integral {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t N,MeasurableSet[m] N → P N=0 → MeasurableSet[F t] N)
    (X : ClosedTime T → Ω → ℝ) (hX : LocalMProcessWitness P F X) (a : ℝ) :
    ItoCovarianceFormula P F X (fun _ => a) (fun t w => a*X t w) := by
  have hi := identity_ito_integral P hT F hF hle hnull X hX
  have hh := hi.add_smul P F hF hle X X X (fun _ => 1) (fun _ => 1) hi (a-1)
  convert hh using 1 <;> funext <;> ring

theorem constant_ito_integral_unique {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t N,MeasurableSet[m] N → P N=0 → MeasurableSet[F t] N)
    (X N : ClosedTime T → Ω → ℝ) (hX : LocalMProcessWitness P F X)
    (hN : LocalMProcessWitness P F N) (a : ℝ) (hi : ItoCovarianceFormula P F X (fun _ => a) N) :
    ∀ᵐ w ∂P,∀ t,t<⊤ → N t w=a*X t w :=
  hi.unique P hT F hF hle hnull X N (fun t w => a*X t w) (fun _ => a)
    hX hN (hX.smul P F a) (constant_ito_integral P hT F hF hle hnull X hX a)

end Asakura.Chapter11

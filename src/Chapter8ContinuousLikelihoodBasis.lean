import Chapter8ContinuousStoppedCoefficient
import Chapter6BoundedVectorConstruction

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter8
open Asakura.Chapter6
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter7
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

theorem continuous_likelihood_basis_constructed {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] {d n : ℕ} (B : BrownianSystem P d)
    (b : Fin n → ℝ × (Fin d → ℝ) → Fin d → ℝ) (hb : ∀ k,Continuous (b k))
    (R : ℝ) (hR : 0≤R) :
    ∃ N : Fin n → Fin d → HalfClosedTime → Ω → ℝ,
      (∀ k j,LocalMProcessWitness P B.F (N k j)) ∧
      (∀ k j,ItoCovarianceFormula P B.F (B.W j)
        (fun z => stoppedBrownianCoefficient P B (b k) R hR j (realTimeClamp z.2) z.1) (N k j)) := by
  have hex k j := by
    let H := stoppedBrownianCoefficient P B (b k) R hR
    obtain ⟨hHa,hHc,_⟩ := continuous_stopped_brownian_coefficient_regular P B (b k) (hb k) R hR
    exact continuous_adapted_ito_exists P (show (0:EReal)<⊤ by simp) B.F B.mono B.le B.null
      (B.W j) (B.martingale j) (fun z => H j (realTimeClamp z.2) z.1)
      (fun r _ _ => hHa j _) (fun _ _ _ w => ((hHc j w).comp real_time_clamp_continuous).continuousOn)
  choose N hN hNI using hex
  exact ⟨N,hN,hNI⟩
end Asakura.Chapter8

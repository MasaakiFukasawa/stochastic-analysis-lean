import Chapter2ActualCovarianceOperator
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

/-- The covariance/Bochner-integral exchange for actual M2 martingales at
each finite time. The covariance operator and the completeness of M2 have
both been constructed in the preceding manuscript proofs. -/
theorem actual_covariance_bochner_exchange
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (N : ClosedTime T → Ω → ℝ) (hN : ContinuousM2Witness P F N)
    (d : ClosedTime T) (hd : d < ⊤) :
    ∃ L : continuousM2Terminal P F →L[ℝ] Lp ℝ 1 P,
      (∀ v, ∃ C : ClosedTime T → Ω → ℝ,
        LocalCovarianceWitness P F (m2ProcessOfTerminal P F v) N C ∧
        ((L v : Lp ℝ 1 P) : Ω → ℝ) =ᵐ[P] C d) ∧
      ∀ (E : Type) [MeasurableSpace E] (μ : Measure E)
        (Z : E → continuousM2Terminal P F), Integrable Z μ →
        Integrable (fun x => L (Z x)) μ ∧
        ∃ C : ClosedTime T → Ω → ℝ,
          LocalCovarianceWitness P F (m2ProcessOfTerminal P F (∫ x, Z x ∂μ)) N C ∧
          C d =ᵐ[P] ((∫ x, L (Z x) ∂μ : Lp ℝ 1 P) : Ω → ℝ) := by
  obtain ⟨L,hbound,hcov⟩ := actual_m2_covariance_operator P hT F hF hle hnull N hN d hd
  refine ⟨L,hcov,?_⟩
  intro E mE μ Z hZ
  letI : CompleteSpace (continuousM2Terminal P F) := continuous_m2_hilbert_complete P F hF hle hnull
  obtain ⟨C,hC,he⟩ := hcov (∫ x, Z x ∂μ)
  refine ⟨L.integrable_comp hZ,C,hC,?_⟩
  rw [L.integral_comp_comm hZ]
  exact he.symm

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.actual_covariance_bochner_exchange

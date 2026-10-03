import Chapter3C2ItoData

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

theorem c2_composition_martingale_part
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T) {d : ℕ}
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X A M : Fin d → ClosedTime T → Ω → ℝ)
    (C : Fin d → Fin d → ClosedTime T → Ω → ℝ)
    (hX : ∀ i, SemimartingaleDecomposition P F (X i) (A i) (M i))
    (hC : ∀ i j, LocalCovarianceWitness P F (M i) (M j) (C i j))
    (f : (Fin d → ℝ) → ℝ) (hf : ContDiff ℝ 2 f)
    (c : ℕ → ℝ) (hc : ∀ k, 0 ≤ c k) (hcm : Monotone c) (hcT : ∀ k, (c k:EReal) < T)
    (hcc : ∀ t, t < ⊤ → ∃ k, t < realTimeClamp (T := T) (c k)) :
    ∃ B L, ∃ N : Fin d → ClosedTime T → Ω → ℝ,
      SemimartingaleDecomposition P F (fun t ω => f (fun i => X i t ω)) B L ∧
      (∀ i, LocalMProcessWitness P F (N i)) ∧
      (∀ i, ItoCovarianceFormula P F (M i)
        (fun z => fderiv ℝ f (fun k => X k (realTimeClamp z.2) z.1) (Pi.single i 1)) (N i)) ∧
      ∀ᵐ ω ∂P, ∀ t, t < ⊤ → L t ω = ∑ i, N i t ω := by
  obtain ⟨I,N,J,hIN,hI,hN,hJv,hJc,hJ⟩ := c2_ito_data_exists P hT F hF hle hnull X A M C hX hC f hf
    c hc hcm hcT hcc
  obtain ⟨B,L,hL,he⟩ := ito_composition_decomposition P hT F hF hle hnull X A M I N C J hX hC f hf
    c hc hcT hcc hIN hI hN hJv hJc hJ
  exact ⟨B,L,N,hL,fun i => (hIN i).martingale,hN,he⟩

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.c2_composition_martingale_part

import Chapter3ScalarIto
import Chapter3LocalSemimartingale

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

theorem zero_variation_integral
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {T : EReal} [Fact (0 ≤ T)] (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n) (H : Ω × ℝ → ℝ) :
    VariationIntegralFormula (T := T) P c hc (fun _ _ => 0) H (fun _ _ => 0) := by
  intro n
  refine ⟨fun _ => 0,?_,?_,?_,?_⟩
  · simp [SignedMeasure.totalVariation_zero]
  · simp
  · simp [SignedMeasure.totalVariation_zero]
  · simp [signedCumulative,signedIntegralRaw,SignedMeasure.toJordanDecomposition_zero]

/-- A local-martingale Ito integral is the corresponding semimartingale
integral, with a constructed zero finite-variation integral. -/
theorem local_ito_as_semimartingale_integral
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F)
    (X Z : ClosedTime T → Ω → ℝ) (H : Ω × ℝ → ℝ)
    (hZ : LocalMProcessWitness P F Z) (hZI : ItoCovarianceFormula P F X H Z)
    (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n) :
    SemimartingaleIntegralFormula P F c hc (fun _ _ => 0) X H Z := by
  exact ⟨(fun _ _ => 0),Z,local_martingale_semimartingale_decomposition P hT F hF Z hZ,
    zero_variation_integral P c hc H,hZI⟩

/-- Scalar Ito formula specialized to local martingales, with actual Ito
and finite-variation integrals rather than postulated differential rules. -/
theorem local_scalar_ito_formula
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X C Z J : ClosedTime T → Ω → ℝ)
    (hX : LocalMProcessWitness P F X) (hC : LocalCovarianceWitness P F X X C)
    (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (c : ℕ → ℝ) (hc : ∀ k, 0 ≤ c k) (hcT : ∀ k, (c k:EReal) < T)
    (hcc : ∀ t, t < ⊤ → ∃ k, t < realTimeClamp (T := T) (c k))
    (hZ : LocalMProcessWitness P F Z)
    (hZI : ItoCovarianceFormula P F X (fun z => deriv f (X (realTimeClamp z.2) z.1)) Z)
    (hJ : VariationIntegralFormula P c hc C
      (fun z => iteratedDeriv 2 f (X (realTimeClamp z.2) z.1)) J) :
    ∀ᵐ ω ∂P, ∀ t, t < ⊤ → f (X t ω) = f (X ⊥ ω)+Z t ω+J t ω/2 := by
  exact scalar_ito_formula P hT F hF hle hnull X (fun _ _ => 0) X C Z J
    (local_martingale_semimartingale_decomposition P hT F hF X hX) hC f hf c hc hcT hcc
    (local_ito_as_semimartingale_integral P hT F hF X Z _ hZ hZI c hc) hJ

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.zero_variation_integral
#print axioms Asakura.Chapter3Complete.local_ito_as_semimartingale_integral
#print axioms Asakura.Chapter3Complete.local_scalar_ito_formula

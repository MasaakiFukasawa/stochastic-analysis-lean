import Chapter2ContinuousVariationIntegral
import Chapter2VariationIntegralFormula
import Chapter2SemimartingaleDecomposition
import Chapter2ItoCharacterizedConstruction

open MeasureTheory Set Filter
open scoped Topology ENNReal Classical
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

/-- Construct both components of the semimartingale integral. Continuity
of the finite-variation integral is proved from continuity of X-A, and
membership in S follows with the original strong A_loc definition. -/
theorem semimartingale_integral_constructed
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X A M Q : ClosedTime T → Ω → ℝ) (hX : SemimartingaleDecomposition P F X A M)
    (hQ : LocalCovarianceWitness P F M M Q)
    (c : ℕ → ℝ) (hc : ∀ n, 0 < c n) (hcm : StrictMono c) (hcT : ∀ n, (c n:EReal) < T)
    (hct : StrictMono (fun n => realTimeClamp (T := T) (c n)))
    (hcut : ∀ n, realTimeClamp (T := T) (c n) < ⊤)
    (hcc : ∀ t, t < ⊤ → ∃ n, t < realTimeClamp (T := T) (c n))
    (hQm : ∀ n ω, MonotoneOn (fun r => Q (realTimeClamp r) ω) (Icc 0 (c n)))
    (hQc : ∀ n ω, ContinuousOn (fun r => Q (realTimeClamp r) ω) (Icc 0 (c n))) :
    ∃ κ : ℕ → Ω → Measure ℝ,
      (∀ n ω, IsFiniteMeasure (κ n ω)) ∧
      (∀ n ω s t, s ≤ t → (κ n ω).real (Ioc s t) =
        pathVariation (fun r => A r ω) (realTimeClamp (intervalClamp 0 (c n) (hc n).le t))-
        pathVariation (fun r => A r ω) (realTimeClamp (intervalClamp 0 (c n) (hc n).le s))) ∧
      ∀ H : Ω × ℝ → ℝ,
        (∀ n, @Measurable _ _
          (progressiveSpace (fun t : Icc (0:ℝ) (c n) => F (realTimeClamp t.val))) inferInstance
          (fun z : Ω × Icc (0:ℝ) (c n) => H (z.1,z.2.val))) →
        (∀ n, ∀ᵐ ω ∂P, Integrable (fun r => H (ω,r)) (κ n ω)) →
        (∀ n, ∀ᵐ ω ∂P, Integrable (fun r => H (ω,r)^2)
          (intervalStieltjes 0 (c n) (hc n).le (fun r => Q (realTimeClamp r) ω) (hQm n ω)
            (fun r hr => (hQc n ω r hr).mono inter_subset_left)).measure) →
        ∃ I J : ClosedTime T → Ω → ℝ,
          SemimartingaleDecomposition P F (fun t ω => I t ω+J t ω) I J ∧
          VariationIntegralFormula P c (fun n => (hc n).le) A H I ∧
          ItoCovarianceFormula P F M H J := by
  obtain ⟨κ,hκ,hsupport,hinc,hconstruct⟩ := continuous_local_variation_integral_constructed P F hF hnull
    c (fun n => (hc n).le) hcm.monotone hcT hcc A hX.variation (hX.variation_continuous P F)
  refine ⟨κ,hκ,hinc,?_⟩
  intro H hH hiA hiM
  obtain ⟨ξ,I,hI,hIc,hξ,hdom,heI⟩ := hconstruct H hH hiA
  obtain ⟨J,hJ,hJchar⟩ := ito_integral_exists_with_covariance_characterization P hT F hF hle hnull
    M Q hX.martingale hQ c hc hcm hcT hct hcut hcc hQm hQc H hH hiM
  refine ⟨I,J,⟨hI,hJ,fun ω t ht => (hIc ω t ht).add (hJ.path P F ω t ht),fun _ _ _ => rfl⟩,?_,hJchar⟩
  exact variation_integral_formula_of_construction P c (fun n => (hc n).le) A I H κ ξ hsupport hξ hdom hiA heI

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.semimartingale_integral_constructed

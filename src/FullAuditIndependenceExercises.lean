import FullAuditRegressionConditional
import Mathlib.MeasureTheory.MeasurableSpace.MeasurablyGenerated

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace Asakura.FullAudit

/-- Independence in the manuscript's conditional-expectation definition is
exactly the product rule on measurable events. -/
theorem conditional_independence_iff {Ω : Type*} {G H m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (hG : G ≤ m) (hH : H ≤ m) :
    (∀ X : Ω → ℝ, StronglyMeasurable[H] X → Integrable X P →
      P[X | G] =ᵐ[P] (fun _ => ∫ ω, X ω ∂P)) ↔
    (∀ A B : Set Ω, MeasurableSet[G] A → MeasurableSet[H] B → P (A ∩ B) = P A * P B) := by
  constructor
  · intro h A B hA hB
    let X : Ω → ℝ := B.indicator (fun _ => 1)
    have hmX : StronglyMeasurable[H] X := stronglyMeasurable_const.indicator hB
    have hiX : Integrable X P := (integrable_const _).indicator (hH _ hB)
    have hc := h X hmX hiX
    have he : ∫ ω in A, X ω ∂P = P.real A * P.real B := by
      calc
        _ = ∫ ω in A, P[X | G] ω ∂P := (setIntegral_condExp hG hiX hA).symm
        _ = ∫ ω in A, (∫ ω, X ω ∂P) ∂P := integral_congr_ae (ae_restrict_of_ae hc)
        _ = _ := by simp [X,integral_indicator (hH _ hB),smul_eq_mul]
    have hi : ∫ ω in A, X ω ∂P = P.real (A ∩ B) := by
      simp [X,setIntegral_indicator (hH _ hB),smul_eq_mul]
    rw [hi] at he
    have hh := congrArg ENNReal.ofReal he
    simpa only [Measure.real, ENNReal.ofReal_mul (ENNReal.toReal_nonneg),
      ENNReal.ofReal_toReal (measure_ne_top P _)] using hh
  · intro h X hmX hiX
    have hind : Indep H G P := (Indep_iff _ _ P).mpr (by
      intro B A hB hA
      simpa only [inter_comm,mul_comm] using h A B hA hB)
    exact condExp_indep_eq hH hG hmX hind

/-- The symmetry demanded in the first independence exercise. -/
theorem conditional_independence_symmetric {Ω : Type*} {G H m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (hG : G ≤ m) (hH : H ≤ m) :
    (∀ X : Ω → ℝ, StronglyMeasurable[H] X → Integrable X P →
      P[X | G] =ᵐ[P] (fun _ => ∫ ω, X ω ∂P)) ↔
    (∀ X : Ω → ℝ, StronglyMeasurable[G] X → Integrable X P →
      P[X | H] =ᵐ[P] (fun _ => ∫ ω, X ω ∂P)) := by
  rw [conditional_independence_iff P hG hH,conditional_independence_iff P hH hG]
  constructor <;> intro h A B hA hB <;> simpa only [inter_comm,mul_comm] using h B A hB hA

/-- The four-set sigma algebras in the second independence exercise. -/
theorem binary_event_independence {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (A B : Set Ω)
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    Indep (MeasurableSpace.generateFrom {A}) (MeasurableSpace.generateFrom {B}) P ↔
      P (A ∩ B) = P A * P B := by
  rw [← IndepSet_iff_Indep]
  exact indepSet_iff_measure_inter_eq_mul hA hB P

end Asakura.FullAudit

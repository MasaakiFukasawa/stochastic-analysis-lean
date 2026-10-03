import Chapter12ProbabilityTrim
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

open MeasureTheory Set
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/-- Conditioning on past information commutes with restricting the ambient
probability space to terminal information, for terminal-measurable variables. -/
theorem conditional_expectation_on_terminal_space {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (mT mS : MeasurableSpace Ω) (hT : mT ≤ m) (hS : mS ≤ mT)
    (u q : Ω → ℝ) (hum : Measurable[mT] u) (hqm : Measurable[mS] q)
    (hu : Integrable u P) (hq : Integrable q P)
    (he : q =ᵐ[P] P[u|mS]) :
    letI : MeasurableSpace Ω := mT
    q =ᵐ[P.trim hT] (P.trim hT)[u|mS] := by
  letI : MeasurableSpace Ω := m
  have hqT := hqm.mono hS le_rfl
  have hut := hu.trim hT hum.stronglyMeasurable
  have hqt := hq.trim hT hqT.stronglyMeasurable
  have hint (s : Set Ω) (hs : MeasurableSet[mS] s) :
      (∫ w in s,q w ∂P)=∫ w in s,u w ∂P :=
    (integral_congr_ae (ae_restrict_of_ae he)).trans (setIntegral_condExp (hS.trans hT) hu hs)
  have hintT (s : Set Ω) (hs : MeasurableSet[mS] s) :
      (∫ w in s,q w ∂P.trim hT)=∫ w in s,u w ∂P.trim hT := by
    rw [← setIntegral_trim hT hqT.stronglyMeasurable (hS s hs),
      ← setIntegral_trim hT hum.stronglyMeasurable (hS s hs)]
    exact hint s hs
  letI := probability_trim P mT hT
  letI : MeasurableSpace Ω := mT
  exact ae_eq_condExp_of_forall_setIntegral_eq hS hut
    (fun s _ _ => hqt.integrableOn) (fun s hs _ => hintT s hs) hqm.aestronglyMeasurable

end Asakura.Chapter12

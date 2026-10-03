import Chapter8SDECanonicalIdentification
import Chapter8InvariantMeasureFromTests
import Chapter8AdditivePathMap

open MeasureTheory Set
open scoped NNReal
namespace Asakura.Chapter8
open Asakura.Chapter4 Asakura.Chapter3Complete Asakura.FullAudit
open Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

/-- Construct the jointly measurable endpoint representing the actual
SDE transition laws and identify its propagated probability measure. -/
theorem actual_invariant_law {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d n : ℕ}
    (B : BrownianSystem P n) (b : (Fin d → ℝ) → (Fin d → ℝ))
    (σ : Fin d → Fin n → ℝ) (L : ℝ≥0) (hb : LipschitzWith L b)
    (Z : (Fin d → ℝ) → HalfClosedTime → Ω → Fin d → ℝ)
    (hZ : ∀ x,VectorSDESolution P B.F B.W (fun i y => b y i) (fun i j _ => σ i j) (fun _ => x) (Z x))
    (π : Measure (Fin d → ℝ)) [IsProbabilityMeasure π] (T : ℝ) (hT : 0≤T)
    (htest : ∀ f : (Fin d → ℝ) → ℝ, ContDiff ℝ (⊤:ℕ∞) f → HasCompactSupport f →
      (∫ x,(∫ w,f (Z x (realTimeClamp T) w) ∂P) ∂π)=∫ x,f x ∂π) :
    ∃ Y : (Fin d → ℝ) × Ω → (Fin d → ℝ), Measurable Y ∧
      (∀ x,(fun w => Y (x,w))=ᵐ[P] Z x (realTimeClamp T)) ∧ (π.prod P).map Y=π := by
  obtain ⟨V,hVm,hV⟩ := brownian_forcing_path P B σ T
  obtain ⟨S,hSc,hS⟩ := additive_path_map_exists b L hb T hT
  let Y := fun p : (Fin d → ℝ) × Ω => S (p.1,V p.2) ⟨T,⟨hT,le_rfl⟩⟩
  have hYm : Measurable Y := (ContinuousMap.measurable_iff_eval.mp
    (hSc.measurable.comp (measurable_fst.prodMk (hVm.comp measurable_snd)))) _
  have hY x : (fun w => Y (x,w))=ᵐ[P] Z x (realTimeClamp T) :=
    (sde_canonical_identification P B b σ L hb T hT V hV S hS x (Z x) (hZ x)).mono
      (fun w hw => (hw ⟨T,⟨hT,le_rfl⟩⟩).symm)
  refine ⟨Y,hYm,hY,?_⟩
  apply invariant_measure_from_tests π P Y hYm
  intro f hf hs
  rw [← htest f hf hs]
  apply integral_congr_ae
  apply ae_of_all
  intro x
  exact integral_congr_ae ((hY x).mono (fun w hw => congrArg f hw))

end Asakura.Chapter8

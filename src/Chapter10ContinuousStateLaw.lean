import Chapter10LinearStateGaussian
import Chapter10StateCentered
import Chapter10StateDriftRestriction

open MeasureTheory ProbabilityTheory Set
open scoped NNReal
namespace Asakura.Chapter10
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

/-- The centered Gaussian law of the actual linear SDE under continuous
coefficients, with bounds required only on the finite time interval. -/
theorem LinearStateWitness.centered_gaussian {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d n : ℕ} (B : BrownianSystem P n)
    (A : ℝ → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) (hA : Continuous A)
    (G : Fin d → Fin n → ℝ → ℝ) (hG : ∀ i j,Continuous (G i j))
    (ξ : Ω → Fin d → ℝ) (hξ : Measurable[B.F ⊥] ξ) (hξg : HasGaussianLaw ξ P)
    (hξ0 : ∫ w,ξ w ∂P=0) (T : ℝ) (hT : 0≤T)
    (N : Fin d → Fin n → HalfClosedTime → Ω → ℝ)
    (X : Ω → C(Icc (0:ℝ) T,Fin d → ℝ))
    (h : LinearStateWitness P B A G ξ T hT N X) :
    HasGaussianLaw X P ∧ ∀ t : Icc (0:ℝ) T,(∫ w,X w t ∂P)=0 := by
  letI : MeasurableSpace Ω := m
  obtain ⟨C,hC⟩ := (isCompact_Icc (a := (0:ℝ)) (b := T)).exists_bound_of_continuousOn hA.continuousOn
  let K : ℝ≥0 := ⟨max C 0,le_max_right _ _⟩
  let A' := fun s => A (projIcc 0 T hT s).val
  have hAc : Continuous A' := hA.comp (continuous_subtype_val.comp continuous_projIcc)
  have hAK s : ‖A' s‖≤K := (hC _ (projIcc 0 T hT s).property).trans (le_max_left C 0)
  have he s (hs : s∈Icc (0:ℝ) T) : A' s=A s := by
    simp only [A']
    congr 1
    simp [projIcc,hs.1,hs.2]
  have h' := h.congr_drift P B A A' G ξ T hT N X he
  exact ⟨h'.gaussian P B A' hAc K hAK G hG ξ hξ hξg T hT N X,
    h'.centered P B A' hAc K hAK G hG ξ hξg.memLp_two hξ0 T hT N X⟩

end Asakura.Chapter10

import Chapter10LinearSolutionOperator
import FullAuditConditionalLimit
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap

open MeasureTheory Set
open scoped NNReal
namespace Asakura.Chapter10
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

/-- Solving the deterministic linear integral equation adds no information
beyond its initial value and the whole forcing path. -/
theorem linear_reconstruction_ae_measurable {Ω : Type*} [m : MeasurableSpace Ω]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (P : Measure Ω) (G : MeasurableSpace Ω) (hG : G≤m)
    (hnull : ∀ Q,MeasurableSet[m] Q → P Q=0 → MeasurableSet[G] Q)
    (A : ℝ → E →L[ℝ] E) (hA : Continuous A)
    (T : ℝ) (hT : 0≤T) (ξ : Ω → E) (hξ : Measurable[G] ξ)
    (Z X : Ω → C(Icc (0:ℝ) T,E)) (hZ : Measurable[G] Z)
    (hXm : Measurable[m] X) (he : ∀ᵐ w ∂P,∀ t,X w t=ξ w+(∫ s in 0..t.val,A s (X w (projIcc 0 T hT s)))+Z w t) :
    Measurable[G] X := by
  obtain ⟨C,hC⟩ := (isCompact_Icc (a := (0:ℝ)) (b := T)).exists_bound_of_continuousOn hA.continuousOn
  let K : ℝ≥0 := ⟨max C 0,le_max_right _ _⟩
  let A' := fun s => A (projIcc 0 T hT s).val
  have hAc : Continuous A' := hA.comp (continuous_subtype_val.comp continuous_projIcc)
  have hAK s : ‖A' s‖≤K := (hC _ (projIcc 0 T hT s).property).trans (le_max_left C 0)
  have hAe s (hs : s∈Icc (0:ℝ) T) : A' s=A s := by
    simp only [A']
    congr 1
    simp [projIcc,hs.1,hs.2]
  obtain ⟨S,hS⟩ := linear_solution_operator_exists A' hAc K hAK T hT
  have hpath : X=ᵐ[P] (fun w => S (ξ w,Z w)) := by
    filter_upwards [he] with w he
    apply linear_forced_paths_unique A' hAc K hAK T hT (ξ w,Z w) _ _ ?_ (hS _)
    intro t
    rw [he t]
    congr 2
    apply intervalIntegral.integral_congr
    intro s hs
    have hs' : s∈Icc (0:ℝ) t.val := by simpa only [uIcc_of_le t.property.1] using hs
    dsimp only
    rw [hAe s ⟨hs'.1,hs'.2.trans t.property.2⟩]
  exact Asakura.FullAudit.measurable_of_augmented_ae P hG hnull X _ hXm
    (S.continuous.measurable.comp (hξ.prodMk hZ)) hpath

end Asakura.Chapter10

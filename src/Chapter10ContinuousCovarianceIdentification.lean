import Chapter10CovarianceIdentification
import Chapter10StateDriftRestriction

open MeasureTheory Set Filter Matrix
open scoped Topology BigOperators NNReal Matrix.Norms.Elementwise
namespace Asakura.Chapter10
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

/-- Finite-horizon covariance identification for arbitrary continuous coefficients;
no bound over the whole half-line is added to the manuscript assumptions. -/
theorem continuous_covariance_identification {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d n : ℕ} (B : BrownianSystem P n)
    (A : ℝ → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) (hA : Continuous A)
    (G : Fin d → Fin n → ℝ → ℝ) (hG : ∀ i j,Continuous (G i j))
    (ξ : Ω → Fin d → ℝ) (hξ : Measurable[B.F ⊥] ξ) (hξ2 : MemLp ξ 2 P)
    (T : ℝ) (hT : 0≤T) (S : ℝ → Matrix (Fin d) (Fin d) ℝ)
    (hSc : ContinuousOn S (Icc 0 T))
    (hS0 : S 0=(fun i j => ∫ w,ξ w i*ξ w j ∂P))
    (hSd : ∀ t∈Ico 0 T,HasDerivWithinAt S
      ((show Matrix (Fin d) (Fin d) ℝ from fun i j => (A t (Pi.single j 1)) i)*S t+
        S t*(show Matrix (Fin d) (Fin d) ℝ from fun i j => (A t (Pi.single j 1)) i).transpose+
        (show Matrix (Fin d) (Fin d) ℝ from fun i j => ∑ k,G i k t*G j k t)) (Ici t) t) :
    ∃ (N : Fin d → Fin n → HalfClosedTime → Ω → ℝ)
      (X : Ω → C(Icc (0:ℝ) T,Fin d → ℝ)),LinearStateWitness P B A G ξ T hT N X ∧
      ∀ t∈Icc 0 T,(S t).PosSemidef ∧
        S t=(fun i j => ∫ w,X w (projIcc 0 T hT t) i*X w (projIcc 0 T hT t) j ∂P) := by
  letI : MeasurableSpace Ω := m
  obtain ⟨C,hC⟩ := (isCompact_Icc (a := (0:ℝ)) (b := T)).exists_bound_of_continuousOn hA.continuousOn
  let K : ℝ≥0 := ⟨max C 0,le_max_right _ _⟩
  let A' := fun t => A (projIcc 0 T hT t).val
  have hAc : Continuous A' := hA.comp (continuous_subtype_val.comp continuous_projIcc)
  have hAK t : ‖A' t‖≤K := (hC _ (projIcc 0 T hT t).property).trans (le_max_left C 0)
  have he t (ht : t∈Icc (0:ℝ) T) : A' t=A t := by
    have hp : (projIcc 0 T hT t).val=t := by simp [projIcc,ht.1,ht.2]
    simp only [A',hp]
  obtain ⟨N,X,hState,hcov⟩ := linear_covariance_identification P B A' hAc K hAK G hG ξ hξ hξ2 T hT S hSc hS0
    (by intro t ht; simpa only [he t ⟨ht.1,ht.2.le⟩] using hSd t ht)
  exact ⟨N,X,hState.congr_drift P B A' A G ξ T hT N X (fun s hs => (he s hs).symm),hcov⟩

end Asakura.Chapter10

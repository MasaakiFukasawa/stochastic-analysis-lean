import Chapter10ConstructedCovarianceODE
import Chapter10MatrixCovarianceUniqueness

open MeasureTheory Set Filter Matrix
open scoped Topology BigOperators NNReal Matrix.Norms.Elementwise
namespace Asakura.Chapter10
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

/-- A candidate Lyapunov solution is the covariance of the actual constructed
SDE. Positivity is therefore a conclusion, including singular initial data. -/
theorem linear_covariance_identification {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d n : ℕ} (B : BrownianSystem P n)
    (A : ℝ → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) (hA : Continuous A)
    (K : ℝ≥0) (hAK : ∀ t,‖A t‖≤K)
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
  obtain ⟨N,X,hState,hVc,hVp,hV0,hVd⟩ := constructed_covariance_ode P B A hA K hAK G hG ξ hξ hξ2 T hT
  let a : ℝ → Matrix (Fin d) (Fin d) ℝ := fun t i j => (A t (Pi.single j 1)) i
  have hac : Continuous a := continuous_pi (fun i => continuous_pi (fun j =>
    (continuous_apply i).comp (hA.clm_apply continuous_const)))
  have hbc : Continuous (fun t => (a t).transpose) := continuous_pi (fun i => continuous_pi (fun j =>
    (continuous_apply j).comp (hA.clm_apply continuous_const)))
  obtain ⟨C₁,hC₁⟩ := (isCompact_Icc (a := (0:ℝ)) (b := T)).exists_bound_of_continuousOn hac.continuousOn
  obtain ⟨C₂,hC₂⟩ := (isCompact_Icc (a := (0:ℝ)) (b := T)).exists_bound_of_continuousOn hbc.continuousOn
  let C := max 0 (max C₁ C₂)
  have hv := matrix_covariance_unique _ S a (fun t => (a t).transpose)
    (fun t i j => ∑ k,G i k t*G j k t) T C (le_max_left _ _)
    hVc.continuousOn hSc hVd hSd
    (fun t ht => (hC₁ t ⟨ht.1,ht.2.le⟩).trans ((le_max_left C₁ C₂).trans (le_max_right _ _)))
    (fun t ht => (hC₂ t ⟨ht.1,ht.2.le⟩).trans ((le_max_right C₁ C₂).trans (le_max_right _ _)))
    (hV0.trans hS0.symm)
  refine ⟨N,X,hState,?_⟩
  intro t ht
  exact ⟨hv t ht ▸ hVp t,(hv t ht).symm⟩

end Asakura.Chapter10

import Chapter10InnovationCovarianceConstruction
import Chapter10InnovationPastOrthogonality
import Chapter10GaussianPathHistory
import Chapter10AugmentedInitial

open MeasureTheory ProbabilityTheory Set Matrix
open scoped Topology BigOperators Matrix.Norms.Elementwise
namespace Asakura.Chapter10
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

/-- Actual error and innovation paths with the covariance and entire-history
independence proved, including the zero-variance initial-error case. -/
theorem innovation_history_construction {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d q r : ℕ} (B : BrownianSystem P (q+r))
    (F S : ℝ → Matrix (Fin d) (Fin d) ℝ) (G : ℝ → Matrix (Fin d) (Fin q) ℝ)
    (K : ℝ → Matrix (Fin d) (Fin r) ℝ) (D : ℝ → Matrix (Fin r) (Fin r) ℝ)
    (L : ℝ → Matrix (Fin r) (Fin d) ℝ)
    (hF : Continuous F) (hS : Continuous S) (hG : Continuous G)
    (hK : Continuous K) (hD : Continuous D) (hL : Continuous L)
    (ξ : Ω → Fin d → ℝ) (hξ : Measurable[B.F ⊥] ξ) (hξg : HasGaussianLaw ξ P)
    (hξ0 : ∫ w,ξ w ∂P=0) (T : ℝ) (hT : 0≤T)
    (hinit : S 0=(fun i j => ∫ w,ξ w i*ξ w j ∂P))
    (hSym : ∀ t∈Ico 0 T,(S t).transpose=S t)
    (hcancel : ∀ t∈Ico 0 T,S t*(L t).transpose=K t*D t)
    (hSd : ∀ t∈Ico 0 T,HasDerivWithinAt S
      (F t*S t+S t*(F t).transpose+G t*(G t).transpose+(K t*D t)*(K t*D t).transpose) (Ici t) t) :
    let A := fun t => matrixOperatorMap (finiteBlocks (F t) 0 (L t) (0 : Matrix (Fin r) (Fin r) ℝ))
    let E := fun i j t => finiteBlocks (G t) (-(K t*D t)) (0 : Matrix (Fin r) (Fin q) ℝ) (1 : Matrix (Fin r) (Fin r) ℝ) i j
    ∃ N X,LinearStateWitness P B A E (fun w => extendZero (r := r) (ξ w)) T hT N X ∧
      HasGaussianLaw X P ∧
      (∀ t∈Icc 0 T,finiteBlocks (S t) 0 0 (t • (1 : Matrix (Fin r) (Fin r) ℝ))=
        (fun i j => ∫ w,X w (projIcc 0 T hT t) i*X w (projIcc 0 T hT t) j ∂P)) ∧
      ∀ t : Icc (0:ℝ) T,IndepFun (fun w i => X w t (headIndex i))
        (fun w (z : {s : Icc (0:ℝ) T // s.val≤t.val} × Fin r) => X w z.1.val (tailIndex z.2)) P := by
  letI : MeasurableSpace Ω := m
  let A := fun t => matrixOperatorMap (finiteBlocks (F t) 0 (L t) (0 : Matrix (Fin r) (Fin r) ℝ))
  let E₀ := fun t => finiteBlocks (G t) (-(K t*D t)) (0 : Matrix (Fin r) (Fin q) ℝ) (1 : Matrix (Fin r) (Fin r) ℝ)
  let E := fun i j t => E₀ t i j
  let ξ₀ := fun w => extendZero (r := r) (ξ w)
  obtain ⟨hξm,hξG,hξz⟩ := augmented_initial_gaussian P (B.F ⊥) (B.le _) (r := r) ξ hξ hξg hξ0
  have hξcov : finiteBlocks (S 0) 0 0 (0 : Matrix (Fin r) (Fin r) ℝ)=
      (fun i j => ∫ w,ξ₀ w i*ξ₀ w j ∂P) := by
    rw [hinit]
    exact (augmented_initial_covariance P (r := r) ξ).symm
  obtain ⟨N,X,hState,hGaussian,hmean,hcov⟩ := innovation_covariance_construction P B F S G K D L
    hF hS hG hK hD hL ξ₀ hξm hξG hξz T hT hξcov hSym hcancel hSd
  have hsame s i j : (∫ w,X w s (headIndex i)*X w s (tailIndex j) ∂P)=0 := by
    have hh := congrFun (congrFun (hcov s.val s.property) (headIndex i)) (tailIndex j)
    have hp : projIcc 0 T hT s.val=s := Subtype.ext (by simp [projIcc,s.property.1,s.property.2])
    simpa only [hp,finiteBlocks_head_tail] using hh.symm
  have hEc : Continuous E₀ := finiteBlocks_continuous G _ _ _ hG
    (hK.matrix_mul hD).neg continuous_const continuous_const
  have hE i j : Continuous (E i j) := (continuous_apply j).comp ((continuous_apply i).comp hEc)
  have hpast := innovation_past_orthogonality P B F L hF E hE ξ₀ hξG.memLp_two T hT N X hState hsame
  have hmeancoord s i : (∫ w,X w s i ∂P)=0 := by
    have hi := (hGaussian.map (ContinuousMap.evalCLM ℝ s)).integrable
    have hh := (show (Fin (d+r) → ℝ) →L[ℝ] ℝ from ContinuousLinearMap.proj i).integral_comp_comm hi
    change (∫ w,X w s i ∂P)=(∫ w,X w s ∂P) i at hh
    rw [hh,hmean]
    rfl
  exact ⟨N,X,hState,hGaussian,hcov,fun t => gaussian_path_error_independent_history P T X
    hState.measurable hGaussian hmeancoord hpast t⟩

end Asakura.Chapter10

import Chapter10RiccatiPositivity
import Chapter10MatrixOperator
import Chapter10KalmanGainAlgebra
import Chapter10CovarianceTraceBound

open MeasureTheory Set Filter Matrix
open scoped Topology BigOperators Matrix.Norms.Elementwise
namespace Asakura.Chapter10
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- Positivity and a matrix norm/trace bound for the manuscript's actual
Riccati coefficients, using the concatenated error noise G and -K D. -/
theorem kalman_local_riccati_bounds {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d q r : ℕ} (B : BrownianSystem P (q+r))
    (A : ℝ → Matrix (Fin d) (Fin d) ℝ) (G : ℝ → Matrix (Fin d) (Fin q) ℝ)
    (C : ℝ → Matrix (Fin r) (Fin d) ℝ) (D J : ℝ → Matrix (Fin r) (Fin r) ℝ)
    (hA : Continuous A) (hG : Continuous G) (hC : Continuous C) (hD : Continuous D) (hJ : Continuous J)
    (ξ : Ω → Fin d → ℝ) (hξ : Measurable[B.F ⊥] ξ) (hξ2 : MemLp ξ 2 P)
    (T : ℝ) (hT : 0≤T) (hJD : ∀ t∈Ico 0 T,J t*D t=1) (hDJ : ∀ t∈Ico 0 T,D t*J t=1)
    (S : ℝ → Matrix (Fin d) (Fin d) ℝ) (hSc : Continuous S)
    (hS0 : S 0=(fun i j => ∫ w,ξ w i*ξ w j ∂P))
    (hSd : ∀ t∈Ico 0 T,HasDerivWithinAt S
      (A t*S t+S t*(A t).transpose+G t*(G t).transpose-S t*((C t).transpose*((J t).transpose*J t)*C t)*S t) (Ici t) t) :
    ∀ t∈Icc 0 T,(S t).PosSemidef ∧ ‖S t‖≤(S t).trace := by
  letI : MeasurableSpace Ω := m
  let K := fun t => S t*(C t).transpose*((J t).transpose*J t)
  have hK : Continuous K := by dsimp [K]; fun_prop
  let F := fun t => matrixOperatorMap (A t-K t*C t)
  have hFc : Continuous F := matrixOperatorMap.continuous.comp (hA.sub (hK.matrix_mul hC))
  let E := fun i k t => errorNoise (G t) (K t) (D t) i k
  have hEc i k : Continuous (E i k) := by
    refine Fin.addCases (fun j => ?_) (fun j => ?_) k
    · simpa only [E,errorNoise,Fin.addCases_left,Function.comp_def] using!
        (continuous_apply j).comp ((continuous_apply i).comp hG)
    · simpa only [E,errorNoise,Fin.addCases_right,Function.comp_def,Pi.neg_apply] using!
        ((continuous_apply j).comp ((continuous_apply i).comp (hK.matrix_mul hD))).neg
  obtain ⟨N,X,hState,hrep⟩ := riccati_solution_positive P B F hFc E hEc ξ hξ hξ2 T hT
    S A (fun t => G t*(G t).transpose) K C (fun t => D t*(D t).transpose) hSc.continuousOn hS0
    (by
      intro t ht
      dsimp only [K]
      rw [kalman_gain_riccati_term]
      exact hSd t ht)
    (fun t ht => kalman_gain_times_noise_covariance (S t) (C t) (D t) (J t) (hJD t ht) (hDJ t ht))
    (fun t _ => matrixOperatorMap_entries (A t-K t*C t))
    (by
      intro t _
      change errorNoise (G t) (K t) (D t)*(errorNoise (G t) (K t) (D t)).transpose=
        G t*(G t).transpose+K t*(D t*(D t).transpose)*(K t).transpose
      exact errorNoise_gram _ _ _)
  intro t ht
  obtain ⟨hpos,heq⟩ := hrep t ht
  refine ⟨hpos,?_⟩
  rw [heq]
  apply covariance_norm_le_trace P (fun i w => X w (projIcc 0 T hT t) i)
  intro i
  apply hState.moment.norm.of_le
    ((measurable_pi_apply i).comp ((continuous_eval_const _).measurable.comp hState.measurable)).aestronglyMeasurable
  exact ae_of_all _ fun w => by
    simpa only [norm_norm,Function.comp_apply] using
      (norm_le_pi_norm (X w (projIcc 0 T hT t)) i).trans ((X w).norm_coe_le_norm _)

end Asakura.Chapter10

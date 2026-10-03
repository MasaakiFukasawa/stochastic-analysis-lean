import Chapter10InnovationHistoryConstruction
import Chapter10RiccatiAlgebra

open MeasureTheory ProbabilityTheory Set Matrix
open scoped Topology BigOperators Matrix.Norms.Elementwise
namespace Asakura.Chapter10
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false

/-- Substitute the manuscript's actual Kalman gain and observation inverse
into the constructed error/innovation history theorem. -/
theorem kalman_innovation_history {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d q r : ℕ} (B : BrownianSystem P (q+r))
    (A S : ℝ → Matrix (Fin d) (Fin d) ℝ) (G : ℝ → Matrix (Fin d) (Fin q) ℝ)
    (C : ℝ → Matrix (Fin r) (Fin d) ℝ) (D J : ℝ → Matrix (Fin r) (Fin r) ℝ)
    (hA : Continuous A) (hS : Continuous S) (hG : Continuous G)
    (hC : Continuous C) (hD : Continuous D) (hJ : Continuous J)
    (ξ : Ω → Fin d → ℝ) (hξ : Measurable[B.F ⊥] ξ) (hξg : HasGaussianLaw ξ P)
    (hξ0 : ∫ w,ξ w ∂P=0) (T : ℝ) (hT : 0≤T)
    (hinit : S 0=(fun i j => ∫ w,ξ w i*ξ w j ∂P))
    (hJD : ∀ t∈Ico 0 T,J t*D t=1) (hDJ : ∀ t∈Ico 0 T,D t*J t=1)
    (hSym : ∀ t∈Ico 0 T,(S t).transpose=S t)
    (hSd : ∀ t∈Ico 0 T,HasDerivWithinAt S
      (A t*S t+S t*(A t).transpose+G t*(G t).transpose-S t*((C t).transpose*((J t).transpose*J t)*C t)*S t) (Ici t) t) :
    let K := fun t => S t*(C t).transpose*((J t).transpose*J t)
    let F := fun t => A t-K t*C t
    let U := fun t => matrixOperatorMap (finiteBlocks (F t) 0 (J t*C t) (0 : Matrix (Fin r) (Fin r) ℝ))
    let E := fun i j t => finiteBlocks (G t) (-(K t*D t)) (0 : Matrix (Fin r) (Fin q) ℝ) (1 : Matrix (Fin r) (Fin r) ℝ) i j
    ∃ N X,LinearStateWitness P B U E (fun w => extendZero (r := r) (ξ w)) T hT N X ∧
      HasGaussianLaw X P ∧
      (∀ t∈Icc 0 T,finiteBlocks (S t) 0 0 (t • (1 : Matrix (Fin r) (Fin r) ℝ))=
        (fun i j => ∫ w,X w (projIcc 0 T hT t) i*X w (projIcc 0 T hT t) j ∂P)) ∧
      ∀ t : Icc (0:ℝ) T,IndepFun (fun w i => X w t (headIndex i))
        (fun w (z : {s : Icc (0:ℝ) T // s.val≤t.val} × Fin r) => X w z.1.val (tailIndex z.2)) P := by
  letI : MeasurableSpace Ω := m
  let K := fun t => S t*(C t).transpose*((J t).transpose*J t)
  have hK : Continuous K := by dsimp [K]; fun_prop
  apply innovation_history_construction P B (fun t => A t-K t*C t) S G K D (fun t => J t*C t)
    (hA.sub (hK.matrix_mul hC)) hS hG hK hD (hJ.matrix_mul hC) ξ hξ hξg hξ0 T hT hinit hSym
  · intro t ht
    dsimp only [K]
    rw [kalman_gain_times_diffusion _ _ _ _ (hJD t ht),transpose_mul,Matrix.mul_assoc]
  · intro t ht
    have hgain := kalman_gain_times_noise_covariance (S t) (C t) (D t) (J t) (hJD t ht) (hDJ t ht)
    have hid := riccati_covariance_identity (A t) (S t) (G t*(G t).transpose) (K t) (C t)
      (D t*(D t).transpose) hgain
    have hnoise : (K t*D t)*(K t*D t).transpose=K t*(D t*(D t).transpose)*(K t).transpose := by
      simp only [transpose_mul,Matrix.mul_assoc]
    rw [hnoise,hid]
    dsimp only [K]
    rw [kalman_gain_riccati_term]
    exact hSd t ht

end Asakura.Chapter10

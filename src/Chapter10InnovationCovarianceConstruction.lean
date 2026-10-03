import Chapter10InnovationFiniteCovariance
import Chapter10ContinuousStateLaw

open MeasureTheory ProbabilityTheory Set Matrix
open scoped Topology BigOperators Matrix.Norms.Elementwise
namespace Asakura.Chapter10
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false

/-- The error and innovation are constructed together. Their actual covariance
is block diagonal, with innovation block t times the identity. -/
theorem innovation_covariance_construction {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d q r : ℕ} (B : BrownianSystem P (q+r))
    (F S : ℝ → Matrix (Fin d) (Fin d) ℝ) (G : ℝ → Matrix (Fin d) (Fin q) ℝ)
    (K : ℝ → Matrix (Fin d) (Fin r) ℝ) (D : ℝ → Matrix (Fin r) (Fin r) ℝ)
    (L : ℝ → Matrix (Fin r) (Fin d) ℝ)
    (hF : Continuous F) (hS : Continuous S) (hG : Continuous G)
    (hK : Continuous K) (hD : Continuous D) (hL : Continuous L)
    (ξ : Ω → Fin (d+r) → ℝ) (hξ : Measurable[B.F ⊥] ξ) (hξg : HasGaussianLaw ξ P)
    (hξ0 : ∫ w,ξ w ∂P=0) (T : ℝ) (hT : 0≤T)
    (hinit : finiteBlocks (S 0) 0 0 (0 : Matrix (Fin r) (Fin r) ℝ)=
      (fun i j => ∫ w,ξ w i*ξ w j ∂P))
    (hSym : ∀ t∈Ico 0 T,(S t).transpose=S t)
    (hcancel : ∀ t∈Ico 0 T,S t*(L t).transpose=K t*D t)
    (hSd : ∀ t∈Ico 0 T,HasDerivWithinAt S
      (F t*S t+S t*(F t).transpose+G t*(G t).transpose+(K t*D t)*(K t*D t).transpose) (Ici t) t) :
    let A := fun t => matrixOperatorMap (finiteBlocks (F t) 0 (L t) (0 : Matrix (Fin r) (Fin r) ℝ))
    let E := fun i j t => finiteBlocks (G t) (-(K t*D t)) (0 : Matrix (Fin r) (Fin q) ℝ) (1 : Matrix (Fin r) (Fin r) ℝ) i j
    ∃ N X,LinearStateWitness P B A E ξ T hT N X ∧ HasGaussianLaw X P ∧
      (∀ t : Icc (0:ℝ) T,(∫ w,X w t ∂P)=0) ∧
      ∀ t∈Icc 0 T,finiteBlocks (S t) 0 0 (t • (1 : Matrix (Fin r) (Fin r) ℝ))=
        (fun i j => ∫ w,X w (projIcc 0 T hT t) i*X w (projIcc 0 T hT t) j ∂P) := by
  letI : MeasurableSpace Ω := m
  let A₀ := fun t => finiteBlocks (F t) 0 (L t) (0 : Matrix (Fin r) (Fin r) ℝ)
  let A := fun t => matrixOperatorMap (A₀ t)
  let E₀ := fun t => finiteBlocks (G t) (-(K t*D t)) (0 : Matrix (Fin r) (Fin q) ℝ) (1 : Matrix (Fin r) (Fin r) ℝ)
  let E := fun i j t => E₀ t i j
  let V := fun t => finiteBlocks (S t) 0 0 (t • (1 : Matrix (Fin r) (Fin r) ℝ))
  have hAc : Continuous A := matrixOperatorMap.continuous.comp
    (finiteBlocks_continuous F _ L _ hF continuous_const hL continuous_const)
  have hEc : Continuous E₀ := finiteBlocks_continuous G _ _ _ hG
    (hK.matrix_mul hD).neg continuous_const continuous_const
  have hE i j : Continuous (E i j) := (continuous_apply j).comp ((continuous_apply i).comp hEc)
  have hVc : Continuous V := finiteBlocks_continuous S _ _ _ hS continuous_const continuous_const
    (continuous_id.smul continuous_const)
  have hV0 : V 0=(fun i j => ∫ w,ξ w i*ξ w j ∂P) := by simpa only [V,zero_smul] using hinit
  obtain ⟨N,X,hState,hcov⟩ := continuous_covariance_identification P B A hAc E hE ξ hξ hξg.memLp_two T hT
    V hVc.continuousOn hV0 (by
      intro t ht
      have hd := finiteBlocks_deriv (r := r) S _ t (hSd t ht)
      have hid := innovation_finite_covariance_identity (F t) (S t) (G t) (K t) (D t) (L t)
        (t • (1 : Matrix (Fin r) (Fin r) ℝ)) (hSym t ht) (hcancel t ht)
      change HasDerivWithinAt V ((show Matrix (Fin (d+r)) (Fin (d+r)) ℝ from fun i j => (A t (Pi.single j 1)) i)*V t+
        V t*(show Matrix (Fin (d+r)) (Fin (d+r)) ℝ from fun i j => (A t (Pi.single j 1)) i).transpose+E₀ t*(E₀ t).transpose) (Ici t) t
      have ha : (fun i j => (A t (Pi.single j 1)) i)=A₀ t := matrixOperatorMap_entries (A₀ t)
      rw [ha]
      rw [hid]
      exact hd)
  obtain ⟨hg,hzero⟩ := hState.centered_gaussian P B A hAc E hE ξ hξ hξg hξ0 T hT N X
  exact ⟨N,X,hState,hg,hzero,fun t ht => (hcov t ht).2⟩

end Asakura.Chapter10

import Chapter10InnovationHistoryConstruction
import Chapter10LinearStateUniqueness
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

/-- Identify any actual solution of the error/innovation equations by path uniqueness. -/
theorem innovation_history_identification {Ω : Type*} [m : MeasurableSpace Ω]
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
    ∀ N X,LinearStateWitness P B A E (fun w => extendZero (r := r) (ξ w)) T hT N X →
      HasGaussianLaw X P ∧
      (∀ t∈Icc 0 T,finiteBlocks (S t) 0 0 (t • (1 : Matrix (Fin r) (Fin r) ℝ))=
        (fun i j => ∫ w,X w (projIcc 0 T hT t) i*X w (projIcc 0 T hT t) j ∂P)) ∧
      ∀ t : Icc (0:ℝ) T,IndepFun (fun w i => X w t (headIndex i))
        (fun w (z : {s : Icc (0:ℝ) T // s.val≤t.val} × Fin r) => X w z.1.val (tailIndex z.2)) P := by
  letI : MeasurableSpace Ω := m
  let A := fun t => matrixOperatorMap (finiteBlocks (F t) 0 (L t) (0 : Matrix (Fin r) (Fin r) ℝ))
  let E₀ := fun t => finiteBlocks (G t) (-(K t*D t)) (0 : Matrix (Fin r) (Fin q) ℝ) (1 : Matrix (Fin r) (Fin r) ℝ)
  let E := fun i j t => E₀ t i j
  have hAc : Continuous A := matrixOperatorMap.continuous.comp
    (finiteBlocks_continuous F _ L _ hF continuous_const hL continuous_const)
  have hEc : Continuous E₀ := finiteBlocks_continuous G _ _ _ hG
    (hK.matrix_mul hD).neg continuous_const continuous_const
  have hE i j : Continuous (E i j) := (continuous_apply j).comp ((continuous_apply i).comp hEc)
  dsimp only
  intro N X hX
  obtain ⟨M,Y,hY,hg,hcov,hind⟩ := innovation_history_construction P B F S G K D L
    hF hS hG hK hD hL ξ hξ hξg hξ0 T hT hinit hSym hcancel hSd
  have he := hY.unique P B A hAc E hE _ T hT M N Y X hX
  refine ⟨hg.congr he,?_,?_⟩
  · intro t ht
    rw [hcov t ht]
    ext i j
    apply integral_congr_ae
    filter_upwards [he] with w hw
    rw [hw]
  · intro t
    exact (hind t).congr
      (he.mono (fun w hw => by dsimp only; rw [hw]))
      (he.mono (fun w hw => by dsimp only; rw [hw]))

end Asakura.Chapter10

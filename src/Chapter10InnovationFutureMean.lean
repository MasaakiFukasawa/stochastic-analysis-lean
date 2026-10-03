import Chapter10ContinuousFutureEquation
import Chapter10FiniteBlockProjection
import Chapter10StateCoordinate
import Chapter10InnovationFiniteCovariance

open MeasureTheory Set Matrix
open scoped BigOperators Matrix.Norms.Elementwise
namespace Asakura.Chapter10
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

lemma finiteBlocks_tail_action {d r : ℕ} (F : Matrix (Fin d) (Fin d) ℝ)
    (L : Matrix (Fin r) (Fin d) ℝ) (x : Fin (d+r) → ℝ) (j : Fin r) :
    matrixOperatorMap (finiteBlocks F 0 L (0 : Matrix (Fin r) (Fin r) ℝ)) x (tailIndex j)=
      ∑ i,L j i*x (headIndex i) := by
  rw [matrixOperatorMap_apply]
  simp only [finiteBlocks,submatrix_mulVec_equiv,fromBlocks_mulVec,Matrix.zero_mulVec,
    add_zero,tailIndex,Function.comp_apply,Equiv.symm_apply_apply,Sum.elim_inr]
  rfl

/-- The conditional centering of the future error removes the innovation
drift. The martingale part is removed using its actual Ito construction. -/
theorem innovation_future_weighted_mean {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d r n : ℕ} (B : BrownianSystem P n)
    (F : ℝ → Matrix (Fin d) (Fin d) ℝ) (L : ℝ → Matrix (Fin r) (Fin d) ℝ)
    (hF : Continuous F) (hL : Continuous L)
    (E : Fin (d+r) → Fin n → ℝ → ℝ) (hE : ∀ i j,Continuous (E i j))
    (ξ : Ω → Fin (d+r) → ℝ) (hξ : MemLp ξ 2 P)
    (T : ℝ) (hT : 0≤T) (N : Fin (d+r) → Fin n → HalfClosedTime → Ω → ℝ)
    (X : Ω → C(Icc (0:ℝ) T,Fin (d+r) → ℝ))
    (h : LinearStateWitness P B
      (fun t => matrixOperatorMap (finiteBlocks (F t) 0 (L t) (0 : Matrix (Fin r) (Fin r) ℝ))) E ξ T hT N X)
    (s t : Icc (0:ℝ) T) (hst : s.val≤t.val)
    (η : Ω → ℝ) (hηm : Measurable[B.F (realTimeClamp s.val)] η) (hη : MemLp η 2 P)
    (hz : ∀ u : Icc (0:ℝ) T,s.val≤u.val → ∀ i,(∫ w,η w*X w u (headIndex i) ∂P)=0)
    (j : Fin r) : (∫ w,η w*X w t (tailIndex j) ∂P)=(∫ w,η w*X w s (tailIndex j) ∂P) := by
  letI : MeasurableSpace Ω := m
  let A := fun u => matrixOperatorMap (finiteBlocks (F u) 0 (L u) (0 : Matrix (Fin r) (Fin r) ℝ))
  have hA : Continuous A := matrixOperatorMap.continuous.comp
    (finiteBlocks_continuous F _ L _ hF continuous_const hL continuous_const)
  have he := h.continuous_future_weighted_equation P B A hA E hE ξ hξ T hT N X s t hst η hηm hη (tailIndex j)
  have hd : (∫ u in s.val..t.val,∫ w,η w*(A u (X w (projIcc 0 T hT u))) (tailIndex j) ∂P)=0 := by
    trans ∫ u in s.val..t.val,(0:ℝ)
    swap
    · simp
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le hst] at hu
    have huT : u∈Icc (0:ℝ) T := ⟨s.property.1.trans hu.1,hu.2.trans t.property.2⟩
    have hp : (projIcc 0 T hT u).val=u := by simp [projIcc,huT.1,huT.2]
    have hf : (fun w => η w*(A u (X w (projIcc 0 T hT u))) (tailIndex j))=
        (fun w => ∑ i,L u j i*(η w*X w (projIcc 0 T hT u) (headIndex i))) := by
      funext w
      rw [finiteBlocks_tail_action,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    dsimp only
    rw [hf,integral_finset_sum]
    · apply Finset.sum_eq_zero
      intro i _
      rw [integral_const_mul,hz _ (by simpa only [hp] using hu.1),mul_zero]
    · intro i _
      exact (hη.integrable_mul (h.coordinate_memLp P B A E ξ T hT N X _ (headIndex i))).const_mul _
  rw [hd,add_zero] at he
  exact he

end Asakura.Chapter10

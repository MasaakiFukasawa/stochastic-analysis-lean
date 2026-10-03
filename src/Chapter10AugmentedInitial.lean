import Chapter10FiniteBlocks
import Chapter10ContinuousStateLaw

open MeasureTheory ProbabilityTheory Set Matrix
open scoped Matrix.Norms.Elementwise
namespace Asakura.Chapter10
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

def extendZero {d r : ℕ} (x : Fin d → ℝ) : Fin (d+r) → ℝ :=
  Sum.elim x (fun _ : Fin r => 0) ∘ finSumFinEquiv.symm

noncomputable def extendZeroCLM (d r : ℕ) : (Fin d → ℝ) →L[ℝ] (Fin (d+r) → ℝ) :=
  LinearMap.toContinuousLinearMap {
    toFun := extendZero
    map_add' := by
      intro x y
      ext i
      rcases hi : finSumFinEquiv.symm i with a|a <;> simp [extendZero,hi]
    map_smul' := by
      intro c x
      ext i
      rcases hi : finSumFinEquiv.symm i with a|a <;> simp [extendZero,hi] }

lemma augmented_initial_covariance {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {d r : ℕ} (ξ : Ω → Fin d → ℝ) :
    (fun i j => ∫ w,extendZero (r := r) (ξ w) i*extendZero (r := r) (ξ w) j ∂P)=
      finiteBlocks (fun i j => ∫ w,ξ w i*ξ w j ∂P) 0 0 (0 : Matrix (Fin r) (Fin r) ℝ) := by
  ext i j
  rcases hi : finSumFinEquiv.symm i with a|a <;>
    rcases hj : finSumFinEquiv.symm j with b|b <;>
    simp [extendZero,finiteBlocks,Matrix.submatrix,hi,hj]

lemma augmented_initial_gaussian {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (F : MeasurableSpace Ω) (hle : F≤m)
    {d r : ℕ} (ξ : Ω → Fin d → ℝ) (hξ : Measurable[F] ξ)
    (hg : HasGaussianLaw ξ P) (h0 : ∫ w,ξ w ∂P=0) :
    Measurable[F] (fun w => extendZero (r := r) (ξ w)) ∧
      HasGaussianLaw (fun w => extendZero (r := r) (ξ w)) P ∧
      (∫ w,extendZero (r := r) (ξ w) ∂P)=0 := by
  letI : MeasurableSpace Ω := m
  let L := extendZeroCLM d r
  have hm : Measurable[F] (fun w => L (ξ w)) := L.continuous.measurable.comp hξ
  have hG := hg.map L
  have hz : (∫ w,L (ξ w) ∂P)=0 := by
    rw [L.integral_comp_comm (hg.memLp_two.integrable (by norm_num)),h0,map_zero]
  exact ⟨hm,hG,hz⟩

end Asakura.Chapter10

import Chapter10SemimartingaleFiniteMap
import Chapter10LinearStateWitness
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Topology.Algebra.Module.FiniteDimension

open MeasureTheory Set Matrix
open scoped BigOperators
namespace Asakura.Chapter10
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

noncomputable def rectangularMatrixMap {d D : ℕ} (Q : Matrix (Fin d) (Fin D) ℝ) :
    (Fin D → ℝ) →L[ℝ] (Fin d → ℝ) := (Matrix.toLin' Q).toContinuousLinearMap

theorem rectangularMatrixMap_apply {d D : ℕ} (Q : Matrix (Fin d) (Fin D) ℝ) (x : Fin D → ℝ) :
    rectangularMatrixMap Q x=Q*ᵥx := Matrix.toLin'_apply Q x

/-- A constant linear change of state transforms the actual stochastic
integrals and drift equation, not merely the distribution of the state. -/
theorem LinearStateWitness.matrix_map {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d D n : ℕ} (B : BrownianSystem P n)
    (A : ℝ → (Fin D → ℝ) →L[ℝ] (Fin D → ℝ)) (hA : Continuous A)
    (F : ℝ → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) (Q : Matrix (Fin d) (Fin D) ℝ)
    (hclosed : ∀ s x,F s (Q*ᵥx)=Q*ᵥ(A s x))
    (G : Fin D → Fin n → ℝ → ℝ) (ξ : Ω → Fin D → ℝ)
    (T : ℝ) (hT : 0≤T) (N : Fin D → Fin n → HalfClosedTime → Ω → ℝ)
    (X : Ω → C(Icc (0:ℝ) T,Fin D → ℝ))
    (h : LinearStateWitness P B A G ξ T hT N X) :
    let L := ContinuousLinearMap.compLeftContinuous ℝ (Icc (0:ℝ) T) (rectangularMatrixMap Q)
    LinearStateWitness P B F (fun i j s => ∑ k,Q i k*G k j s) (fun w => Q*ᵥ(ξ w)) T hT
      (fun i j t w => ∑ k,Q i k*N k j t w) (fun w => L (X w)) := by
  let L := ContinuousLinearMap.compLeftContinuous ℝ (Icc (0:ℝ) T) (rectangularMatrixMap Q)
  have hm : Measurable (fun w => L (X w)) := L.continuous.measurable.comp h.measurable
  have hLp : MemLp (fun w => L (X w)) 2 P := by
    apply (h.moment.norm.const_mul ‖L‖).of_le hm.aestronglyMeasurable
    exact ae_of_all _ fun w => (L.le_opNorm (X w)).trans (le_abs_self _)
  refine ⟨?_,?_,hm,hLp,?_⟩
  · intro i j
    exact local_martingale_finset_sum P (by simp : (0:EReal)<⊤) B.F B.mono B.le Finset.univ
      (fun k t w => Q i k*N k j t w) (fun k _ => (h.noise k j).smul P B.F (Q i k))
  · intro i j
    exact ito_weighted_sum P (by simp : (0:EReal)<⊤) B.F B.mono B.le B.null (B.W j) (B.martingale j)
      (fun k => N k j) (fun k z => G k j z.2) (Q i) (fun k => h.ito k j)
  · intro i
    have hh := semimartingale_weighted_sum P (by simp : (0:EReal)<⊤) B.F B.mono B.le
      (fun k t w => X w (finitePrefixTime T hT t) k)
      (fun k t w => ξ w k+∫ s in 0..(finitePrefixTime T hT t).val,(A s (X w (projIcc 0 T hT s))) k)
      (fun k t w => ∑ j,N k j (min (realTimeClamp T) t) w) (Q i) h.decomposition
    have hd : (fun (t : HalfClosedTime) w => (Q*ᵥξ w) i+
        ∫ s in 0..(finitePrefixTime T hT t).val,F s (L (X w) (projIcc 0 T hT s)) i)=
        (fun t w => ∑ k,Q i k*(ξ w k+∫ s in 0..(finitePrefixTime T hT t).val,(A s (X w (projIcc 0 T hT s))) k)) := by
      funext t w
      have hi k : IntervalIntegrable (fun s => Q i k*(A s (X w (projIcc 0 T hT s))) k)
          volume 0 (finitePrefixTime T hT t).val :=
        (((continuous_apply k).comp (hA.clm_apply ((X w).continuous.comp continuous_projIcc))).const_mul _).intervalIntegrable _ _
      have he s : F s (L (X w) (projIcc 0 T hT s)) i=
          ∑ k,Q i k*(A s (X w (projIcc 0 T hT s))) k := by
        change F s (rectangularMatrixMap Q (X w (projIcc 0 T hT s))) i=_
        rw [rectangularMatrixMap_apply,hclosed]
        rfl
      simp_rw [he]
      rw [intervalIntegral.integral_finsetSum (fun k _ => hi k)]
      simp only [Matrix.mulVec,dotProduct,Finset.mul_sum,mul_add,Finset.sum_add_distrib,
        intervalIntegral.integral_const_mul]
    have hn : (fun (t : HalfClosedTime) w => ∑ j,∑ k,Q i k*N k j (min (realTimeClamp T) t) w)=
        (fun t w => ∑ k,Q i k*(∑ j,N k j (min (realTimeClamp T) t) w)) := by
      funext t w
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    change SemimartingaleDecomposition P B.F
      (fun t w => (rectangularMatrixMap Q (X w (finitePrefixTime T hT t))) i) _ _
    simp only [rectangularMatrixMap_apply,Matrix.mulVec,dotProduct] at hd ⊢
    rw [hd,hn]
    exact hh

end Asakura.Chapter10

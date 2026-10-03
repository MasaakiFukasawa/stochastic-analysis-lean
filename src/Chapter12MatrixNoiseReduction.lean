import Chapter12RectangularWhitening
import Chapter12BrownianOrthonormalRows
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Analysis.Normed.Module.FiniteDimension

open MeasureTheory Matrix
open scoped BigOperators
namespace Asakura.Chapter12
open Asakura.Chapter4
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

theorem matrix_noise_reduction {Ω:Type*} [MeasurableSpace Ω]
    (P:Measure Ω) [IsProbabilityMeasure P] {n d:ℕ} (B:BrownianSystem P d)
    (σ:Matrix (Fin n) (Fin d) ℝ) (hσ:(σ*σ.transpose).PosDef) :
    ∃L:(Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ),∃C:BrownianSystem P n,
      ∀t w,L (fun i => C.W i t w)=σ.mulVec (fun j => B.W j t w) := by
  obtain ⟨L,A,hL,hLs,hLL,hA,hLA⟩ := rectangular_whitening σ hσ
  have hrows:∀i j,∑k,A i k*A j k=if i=j then 1 else 0 := by
    intro i j
    have h := congrArg (fun M:Matrix (Fin n) (Fin n) ℝ => M i j) hA
    simpa only [Matrix.mul_apply,Matrix.transpose_apply,Matrix.one_apply] using h
  let e := (L.toLinearEquiv (Pi.basisFun ℝ (Fin n)) ((Matrix.isUnit_iff_isUnit_det L).mp hL)).toContinuousLinearEquiv
  refine ⟨e,brownianOrthonormalRows P B A hrows,?_⟩
  intro t w
  change L.mulVec (A.mulVec (fun j => B.W j t w))=σ.mulVec (fun j => B.W j t w)
  rw [Matrix.mulVec_mulVec,hLA]
end Asakura.Chapter12
#print axioms Asakura.Chapter12.matrix_noise_reduction

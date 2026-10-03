import Chapter12PolygonalGridOperator
import Mathlib.Analysis.InnerProductSpace.Orthonormal

open scoped RealInnerProductSpace BigOperators
namespace Asakura.Chapter12
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

theorem linear_polygonal_commutation {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) (f : ℝ → E) (h : ℝ) (n : ℕ) (t : ℝ) :
    L (polygonalPath f h n t)=polygonalPath (fun s => L (f s)) h n t := by
  simp only [polygonalPath,map_add,map_sum,map_smul,map_sub]

noncomputable def finiteOrthonormalProjection {I H : Type*} [Fintype I]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] (e : I → H) : H →L[ℝ] H :=
  ∑i,(innerSL ℝ (e i)).smulRight (e i)

theorem finiteOrthonormalProjection_apply {I H : Type*} [Fintype I]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] (e : I → H) (x : H) :
    finiteOrthonormalProjection e x=∑i,inner ℝ (e i) x • e i := by
  simp [finiteOrthonormalProjection]

theorem finiteOrthonormalProjection_fix {I H : Type*} [Fintype I]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (e : I → H) (he : Orthonormal ℝ e) (c : I → ℝ) :
    finiteOrthonormalProjection e (∑i,c i • e i)=∑i,c i • e i := by
  classical
  rw [finiteOrthonormalProjection_apply]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  simp only [inner_sum,inner_smul_right,orthonormal_iff_ite.mp he]
  simp

theorem polygonal_orthonormal_representation {I H : Type*} [Fintype I]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (e : I → H) (he : Orthonormal ℝ e) (f : ℝ → H) (h : ℝ) (n : ℕ)
    (c : Fin (n+1) → I → ℝ)
    (hc : ∀j : Fin (n+1),f ((j:ℝ)*h)=∑i,c j i • e i) (t : ℝ) :
    polygonalPath f h n t=∑i,inner ℝ (e i) (polygonalPath f h n t) • e i := by
  let P := finiteOrthonormalProjection e
  have hh : P (polygonalPath f h n t)=polygonalPath f h n t := by
    rw [linear_polygonal_commutation,←polygonalGridOperator_samples,←polygonalGridOperator_samples]
    congr 1
    funext j
    rw [hc j]
    exact finiteOrthonormalProjection_fix e he (c j)
  exact hh.symm.trans (finiteOrthonormalProjection_apply e _)
end Asakura.Chapter12
#print axioms Asakura.Chapter12.polygonal_orthonormal_representation

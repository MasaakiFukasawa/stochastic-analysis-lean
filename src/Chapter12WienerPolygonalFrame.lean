import Chapter12LinearPolygonalCommutation
import FullAuditCommonOrthonormal

open MeasureTheory Set
open scoped Topology RealInnerProductSpace
namespace Asakura.Chapter12
open Asakura.FullAudit
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

theorem wiener_polygonal_frame {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (P : Measure Ω) (W : H →ₗᵢ[ℝ] Lp ℝ 2 P)
    (m : ℕ) (e : Fin m → H) (he : Orthonormal ℝ e)
    (f : ℝ → H) (X : ℝ → Ω → ℝ) (h : ℝ) (n : ℕ)
    (c : Fin (n+1) → Fin m → ℝ)
    (hc : ∀j : Fin (n+1),f ((j:ℝ)*h)=∑i,c j i • e i)
    (hX : ∀j : Fin (n+1),X ((j:ℝ)*h)=ᵐ[P] (W (f ((j:ℝ)*h)) : Ω → ℝ)) :
    ∀ᵐw ∂P,∀t : ℝ,polygonalPath (fun s => X s w) h n t=
      ∑i,inner ℝ (e i) (polygonalPath f h n t)*W (e i) w := by
  have hcoord (j : Fin (n+1)) : (W (f ((j:ℝ)*h)) : Ω → ℝ)=ᵐ[P]
      (fun w => ∑i,c j i*W (e i) w) := by
    rw [hc j]
    exact wiener_finite_linearity P W.toLinearMap e (c j)
  filter_upwards [ae_all_iff.mpr hX,ae_all_iff.mpr hcoord] with w hw hcW
  let L : H →L[ℝ] ℝ := ∑i,W (e i) w • innerSL ℝ (e i)
  have hL x : L x=∑i,inner ℝ (e i) x*W (e i) w := by
    simp only [L,ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,smul_eq_mul]
    exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  have hgrid (j : Fin (n+1)) : X ((j:ℝ)*h) w=L (f ((j:ℝ)*h)) := by
    rw [hw j,hcW j,hL,hc j]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    simp only [inner_sum,inner_smul_right,orthonormal_iff_ite.mp he]
    simp
  intro t
  rw [←polygonalGridOperator_samples]
  have hg : (fun j : Fin (n+1) => X ((j:ℝ)*h) w)=(fun j : Fin (n+1) => L (f ((j:ℝ)*h))) := funext hgrid
  rw [hg,polygonalGridOperator_samples (fun s => L (f s)) h n t,←linear_polygonal_commutation,hL]
end Asakura.Chapter12
#print axioms Asakura.Chapter12.wiener_polygonal_frame

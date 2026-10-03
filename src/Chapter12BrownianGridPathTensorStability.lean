import Chapter12BrownianGridScalarStability
import Chapter12GaussianPathTensorBounds
import Chapter12ScalarForcingPath
import Chapter12NaturalBrownianAllOrders

open MeasureTheory Set
open scoped ContDiff NNReal
namespace Asakura.Chapter12
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

theorem brownian_grid_path_tensor_stability {E α : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (b : E → E) (hb : ContDiff ℝ ∞ b)
    (hbound : ∀k:ℕ,1≤k → ∃C:ℝ≥0,∀x,‖iteratedFDeriv ℝ k b x‖≤(C:ℝ))
    (d : ℕ) (T : ℝ) (hT : 0≤T) (v : Fin (d+1) → E) (x : E)
    (S : C(Icc (0:ℝ) T,E) → C(Icc (0:ℝ) T,E)) (hS : ContDiff ℝ ∞ S)
    (hSeq : ∀q t,S q t=q t+∫s in 0..t.val,b (S q (projIcc 0 T hT s)))
    (ell : E →L[ℝ] ℝ)
    (q n n' : α → ℕ) (h h' : α → ℝ)
    (hh : ∀i,0<h i) (hh' : ∀i,0<h' i) (hn : ∀i,0<n i) (hn' : ∀i,0<n' i)
    (hnT : ∀i,(n i:ℝ)*h i=T) (hnT' : ∀i,(n' i:ℝ)*h' i=T)
    (e : ∀i,Fin (q i) → FiniteWienerHilbert d T) (he : ∀i,Orthonormal ℝ (e i)) :
    let H := finiteWienerHilbertData d T
    let L := fun i => kernelForcingPath (e i) (fun j => brownianKernelPolygonal d T j (h i) (n i)) v
    let M := fun i => kernelForcingPath (e i) (fun j => brownianKernelPolygonal d T j (h' i) (n' i)) v
    let F := fun i => scalarForcingPath T S (ContinuousMap.const _ x) (L i) ell
    let G := fun i => scalarForcingPath T S (ContinuousMap.const _ x) (M i) ell
    ∀k:ℕ,∃C:ℝ,0≤C ∧ ∀i z,
      ‖gaussianPathTensor H (e i) (F i) k z-gaussianPathTensor H (e i) (G i) k z‖≤
        C*(‖S (ContinuousMap.const _ x+L i z)-S (ContinuousMap.const _ x+M i z)‖+
          (Real.sqrt (h i)+Real.sqrt (h' i))) := by
  intro H L M F G k
  obtain ⟨C,hC,hbC⟩ := brownian_grid_scalar_stability b hb hbound d T hT v x S hS hSeq ell
    q n n' h h' hh hh' hn hn' hnT hnT' e he (k+1) (by omega)
  refine ⟨C,hC,?_⟩
  intro i z
  apply gaussianPathTensor_difference_le H (e i) (he i) (F i) (G i) k z _ (by positivity)
  intro t
  have hF := scalarForcingPath_smooth T S hS (ContinuousMap.const _ x) (L i) ell
  have hG := scalarForcingPath_smooth T S hS (ContinuousMap.const _ x) (M i) ell
  simp_rw [←path_derivative_evaluation (F i) hF,←path_derivative_evaluation (G i) hG]
  exact hbC i z t
end Asakura.Chapter12
#print axioms Asakura.Chapter12.brownian_grid_path_tensor_stability

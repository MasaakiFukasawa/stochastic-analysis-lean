import Chapter12BrownianGridODEBounds
import Chapter12ScalarForcingPath
import Chapter12AffineODEUniformStability
import Chapter12BrownianKernelForcingBounds
import Chapter12KernelForcingPath

open MeasureTheory Set
open scoped Topology ContDiff NNReal
namespace Asakura.Chapter12
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

theorem brownian_grid_scalar_bounds {E α : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (b : E → E) (hb : ContDiff ℝ ∞ b)
    (hbound : ∀k:ℕ,1≤k → ∃C:ℝ≥0,∀x,‖iteratedFDeriv ℝ k b x‖≤(C:ℝ))
    (d : ℕ) (T : ℝ) (hT : 0≤T) (v : Fin (d+1) → E) (x : E)
    (S : C(Icc (0:ℝ) T,E) → C(Icc (0:ℝ) T,E)) (hS : ContDiff ℝ ∞ S)
    (hSeq : ∀q t,S q t=q t+∫s in 0..t.val,b (S q (projIcc 0 T hT s)))
    (ell : E →L[ℝ] ℝ)
    (q n : α → ℕ) (h : α → ℝ)
    (hh : ∀i,0<h i) (hn : ∀i,0<n i) (hnT : ∀i,(n i:ℝ)*h i=T)
    (e : ∀i,Fin (q i) → FiniteWienerHilbert d T) (he : ∀i,Orthonormal ℝ (e i)) :
    let L := fun i => kernelForcingPath (e i) (fun j => brownianKernelPolygonal d T j (h i) (n i)) v
    ∀k:ℕ,1≤k → ∃C:ℝ,0≤C ∧ ∀i z t,
      Real.sqrt (∑j : Fin k → Fin (q i),
        ‖(iteratedFDeriv ℝ k (scalarForcingPath T S (ContinuousMap.const _ x) (L i) ell) z
          (fun r => Pi.single (j r) 1)) t‖^2)≤C := by
  intro L
  intro k hk
  obtain ⟨C,hC,hbC⟩ := brownian_grid_ode_bounds b hb hbound d T hT v x S hS hSeq q n h hh hn hnT e he k hk
  refine ⟨‖ell‖*C,mul_nonneg (norm_nonneg _) hC,?_⟩
  intro i z t
  have hX : ContDiff ℝ ∞ (fun y => S (ContinuousMap.const _ x+L i y)) :=
    hS.comp (contDiff_const.add (L i).contDiff)
  exact (scalar_path_derivative_array_bound _ hX ell k z
    (fun j : Fin k → Fin (q i) => fun r => Pi.single (j r) 1) t).trans
    (mul_le_mul_of_nonneg_left (hbC i z t) (norm_nonneg _))
end Asakura.Chapter12
#print axioms Asakura.Chapter12.brownian_grid_scalar_bounds

import Chapter12BrownianGridODEEstimates
import Chapter12AffineODEUniformStability
import Chapter12BrownianKernelForcingBounds
import Chapter12KernelForcingPath
import Chapter12ScalarPathArrayDifference

open MeasureTheory Set
open scoped Topology ContDiff NNReal
namespace Asakura.Chapter12
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

theorem brownian_grid_scalar_stability {E α : Type}
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
    let L := fun i => kernelForcingPath (e i) (fun j => brownianKernelPolygonal d T j (h i) (n i)) v
    let M := fun i => kernelForcingPath (e i) (fun j => brownianKernelPolygonal d T j (h' i) (n' i)) v
    let X := fun i z => S (ContinuousMap.const _ x+L i z)
    let Y := fun i z => S (ContinuousMap.const _ x+M i z)
    ∀k:ℕ,1≤k → ∃C:ℝ,0≤C ∧ ∀i z t,
      Real.sqrt (∑j : Fin k → Fin (q i),
        ‖iteratedFDeriv ℝ k (fun y => ell (X i y t)) z (fun r => Pi.single (j r) 1)-
          iteratedFDeriv ℝ k (fun y => ell (Y i y t)) z (fun r => Pi.single (j r) 1)‖^2)≤
        C*(‖X i z-Y i z‖+(Real.sqrt (h i)+Real.sqrt (h' i))) := by
  intro L M X Y
  intro k hk
  obtain ⟨C,hC,hbC⟩ := brownian_grid_ode_stability b hb hbound d T hT v x S hS hSeq
    q n n' h h' hh hh' hn hn' hnT hnT' e he k hk
  refine ⟨‖ell‖*C,mul_nonneg (norm_nonneg _) hC,?_⟩
  intro i z t
  have hX : ContDiff ℝ ∞ (X i) := hS.comp (contDiff_const.add (L i).contDiff)
  have hY : ContDiff ℝ ∞ (Y i) := hS.comp (contDiff_const.add (M i).contDiff)
  have ha := scalar_path_array_difference (X i) (Y i) hX hY ell k z
    (fun j : Fin k → Fin (q i) => fun r => Pi.single (j r) 1) t
  exact ha.trans ((mul_le_mul_of_nonneg_left (hbC i z t) (norm_nonneg _)).trans_eq
    (mul_assoc _ _ _).symm)
end Asakura.Chapter12
#print axioms Asakura.Chapter12.brownian_grid_scalar_stability

import Chapter12AffineODEUniformStability
import Chapter12BrownianKernelForcingBounds
import Chapter12KernelForcingPath

open MeasureTheory Set
open scoped Topology ContDiff NNReal
namespace Asakura.Chapter12
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

theorem brownian_grid_ode_stability {E α : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (b : E → E) (hb : ContDiff ℝ ∞ b)
    (hbound : ∀k:ℕ,1≤k → ∃C:ℝ≥0,∀x,‖iteratedFDeriv ℝ k b x‖≤(C:ℝ))
    (d : ℕ) (T : ℝ) (hT : 0≤T) (v : Fin (d+1) → E) (x : E)
    (S : C(Icc (0:ℝ) T,E) → C(Icc (0:ℝ) T,E)) (hS : ContDiff ℝ ∞ S)
    (hSeq : ∀q t,S q t=q t+∫s in 0..t.val,b (S q (projIcc 0 T hT s)))
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
        ‖(iteratedFDeriv ℝ k (X i) z (fun r => Pi.single (j r) 1)) t-
          (iteratedFDeriv ℝ k (Y i) z (fun r => Pi.single (j r) 1)) t‖^2)≤
        C*(‖X i z-Y i z‖+(Real.sqrt (h i)+Real.sqrt (h' i))) := by
  intro L M X Y
  have hV : 0≤∑j,‖v j‖ := Finset.sum_nonneg (fun j _ => norm_nonneg _)
  exact affine_ode_uniform_stability b hb hbound T hT S hS hSeq q
    (fun _ => ContinuousMap.const _ x) (fun _ => ContinuousMap.const _ x) L M
    ((∑j,‖v j‖)*Real.sqrt T) (∑j,‖v j‖) (mul_nonneg hV (Real.sqrt_nonneg _)) hV
    (fun i => Real.sqrt (h i)+Real.sqrt (h' i)) (fun i => add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    (fun i t => brownian_kernel_forcing_bounds d T (q i) (e i) (he i) v (h i) (hh i) (n i) (hn i) (hnT i) t)
    (fun i t => brownian_kernel_forcing_bounds d T (q i) (e i) (he i) v (h' i) (hh' i) (n' i) (hn' i) (hnT' i) t)
    (fun i t => brownian_kernel_forcing_difference d T (q i) (e i) (he i) v (h i) (h' i) (hh i) (hh' i)
      (n i) (n' i) (hn i) (hn' i) (hnT i) (hnT' i) t)
end Asakura.Chapter12
#print axioms Asakura.Chapter12.brownian_grid_ode_stability

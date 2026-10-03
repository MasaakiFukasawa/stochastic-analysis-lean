import Chapter12BrownianKernelPolygonal
import Chapter12KernelForcingDifference

open Set
namespace Asakura.Chapter12
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

theorem brownian_kernel_difference_bound (d : ℕ) (T : ℝ) (i : Fin (d+1))
    (h h' : ℝ) (hh : 0<h) (hh' : 0<h') (n n' : ℕ) (hn : 0<n) (hn' : 0<n')
    (hnT : (n:ℝ)*h=T) (hnT' : (n':ℝ)*h'=T) (t : Icc (0:ℝ) T) :
    ‖brownianKernelPolygonal d T i h n t-brownianKernelPolygonal d T i h' n' t‖≤Real.sqrt h+Real.sqrt h' := by
  exact (norm_sub_le_norm_sub_add_norm_sub _ (brownianTimeDirection (i,t)) _).trans
    (add_le_add (brownian_kernel_polygonal_bounds d T i h hh n hn hnT t).2
      (by simpa only [norm_sub_rev] using (brownian_kernel_polygonal_bounds d T i h' hh' n' hn' hnT' t).2))

theorem brownian_kernel_forcing_bounds {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (d : ℕ) (T : ℝ) (m : ℕ) (e : Fin m → FiniteWienerHilbert d T) (he : Orthonormal ℝ e)
    (v : Fin (d+1) → E) (h : ℝ) (hh : 0<h) (n : ℕ) (hn : 0<n) (hnT : (n:ℝ)*h=T)
    (t : Icc (0:ℝ) T) :
    Real.sqrt (∑j,‖kernelForcingOperator e (fun i => brownianKernelPolygonal d T i h n t) v (Pi.single j 1)‖^2)≤
      (∑i,‖v i‖)*Real.sqrt T := by
  apply (kernelForcingOperator_array_bound e he _ v).trans
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left
    (brownian_kernel_polygonal_bounds d T i h hh n hn hnT t).1 (norm_nonneg _))

theorem brownian_kernel_forcing_difference {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (d : ℕ) (T : ℝ) (m : ℕ) (e : Fin m → FiniteWienerHilbert d T) (he : Orthonormal ℝ e)
    (v : Fin (d+1) → E) (h h' : ℝ) (hh : 0<h) (hh' : 0<h') (n n' : ℕ) (hn : 0<n) (hn' : 0<n')
    (hnT : (n:ℝ)*h=T) (hnT' : (n':ℝ)*h'=T) (t : Icc (0:ℝ) T) :
    Real.sqrt (∑j,‖kernelForcingOperator e (fun i => brownianKernelPolygonal d T i h n t) v (Pi.single j 1)-
      kernelForcingOperator e (fun i => brownianKernelPolygonal d T i h' n' t) v (Pi.single j 1)‖^2)≤
      (∑i,‖v i‖)*(Real.sqrt h+Real.sqrt h') := by
  apply (kernelForcingOperator_difference_bound e he _ _ v).trans
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left
    (brownian_kernel_difference_bound d T i h h' hh hh' n n' hn hn' hnT hnT' t) (norm_nonneg _))
end Asakura.Chapter12
#print axioms Asakura.Chapter12.brownian_kernel_forcing_difference

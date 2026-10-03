import Chapter9GaussianAllOrders

open Set
open scoped ContDiff
namespace Asakura.Chapter9
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

theorem ou_backward_joint_smooth {d : ℕ} (x : Fin d → ℝ) :
    ContDiffOn ℝ ∞ (fun q : ℝ × (Fin d → ℝ) =>
      gaussianKernel (Real.exp (-q.1)) (1-Real.exp (-2*q.1)) q.2 x) {q | 0<q.1} := by
  unfold gaussianKernel
  apply ContDiffOn.exp
  apply ContDiffOn.sub (ou_prefactor_smooth d)
  apply ContDiffOn.div
  · apply ContDiffOn.sum
    intro i _
    fun_prop
  · fun_prop
  · intro q hq
    exact mul_ne_zero (by norm_num) (ou_variance_positive q.1 hq).ne'
end Asakura.Chapter9

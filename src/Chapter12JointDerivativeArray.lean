import Chapter12ProductArrayNorm
import Chapter12CompositionHilbertArray

open scoped ContDiff
namespace Asakura.Chapter12
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

theorem joint_derivative_array_bound {N G E F:Type*} [Fintype N]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f:G → E) (g:G → F) (hf:ContDiff ℝ ∞ f) (hg:ContDiff ℝ ∞ g)
    (k:ℕ) (z:G) (e:N → G) :
    Real.sqrt (∑a:Fin k → N,‖iteratedFDeriv ℝ k (fun x => (f x,g x)) z (e ∘ a)‖^2)≤
      Real.sqrt (∑a:Fin k → N,‖iteratedFDeriv ℝ k f z (e ∘ a)‖^2)+
      Real.sqrt (∑a:Fin k → N,‖iteratedFDeriv ℝ k g z (e ∘ a)‖^2) := by
  rw [iteratedFDeriv_prodMk hf.contDiffAt hg.contDiffAt (by simp)]
  exact product_array_norm_le _ _

theorem joint_derivative_array_difference_bound {N G E F:Type*} [Fintype N]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f f':G → E) (g g':G → F) (hf:ContDiff ℝ ∞ f) (hf':ContDiff ℝ ∞ f')
    (hg:ContDiff ℝ ∞ g) (hg':ContDiff ℝ ∞ g') (k:ℕ) (z:G) (e:N → G) :
    Real.sqrt (∑a:Fin k → N,‖iteratedFDeriv ℝ k (fun x => (f x,g x)) z (e ∘ a)-
      iteratedFDeriv ℝ k (fun x => (f' x,g' x)) z (e ∘ a)‖^2)≤
      Real.sqrt (∑a:Fin k → N,‖iteratedFDeriv ℝ k f z (e ∘ a)-iteratedFDeriv ℝ k f' z (e ∘ a)‖^2)+
      Real.sqrt (∑a:Fin k → N,‖iteratedFDeriv ℝ k g z (e ∘ a)-iteratedFDeriv ℝ k g' z (e ∘ a)‖^2) := by
  rw [iteratedFDeriv_prodMk hf.contDiffAt hg.contDiffAt (by simp),
    iteratedFDeriv_prodMk hf'.contDiffAt hg'.contDiffAt (by simp)]
  exact product_array_norm_le _ _
end Asakura.Chapter12
#print axioms Asakura.Chapter12.joint_derivative_array_difference_bound

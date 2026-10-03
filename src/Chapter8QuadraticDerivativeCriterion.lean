import Chapter8FlowTaylorBound
import Mathlib.Analysis.Calculus.FDeriv.Basic

open Filter
open scoped Topology
namespace Asakura.Chapter8
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false

/-- A uniform quadratic remainder proves the Frechet derivative; the
variational process need not be assumed to be a derivative beforehand. -/
theorem derivative_of_quadratic_remainder {E G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (f : E → G) (D : E →L[ℝ] G) (x : E) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ h,‖f (x+h)-f x-D h‖ ≤ C*‖h‖^2) : HasFDerivAt f D x := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero,Asymptotics.isLittleO_iff]
  intro ε hε
  filter_upwards [Metric.ball_mem_nhds (0:E) (show 0<ε/(C+1) by positivity)] with h hh
  have hn : ‖h‖<ε/(C+1) := by simpa only [Metric.mem_ball,dist_zero_right] using hh
  have hs : C*‖h‖ ≤ ε := by
    have ht := (lt_div_iff₀ (show 0<C+1 by positivity)).mp hn
    nlinarith [norm_nonneg h]
  exact (hb h).trans (by nlinarith [mul_le_mul_of_nonneg_right hs (norm_nonneg h)])

end Asakura.Chapter8

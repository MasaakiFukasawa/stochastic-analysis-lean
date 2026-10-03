import FullAuditGaussianIBP
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace Asakura.Chapter9
set_option maxHeartbeats 1000000

/-- Differentiate log p twice along a line, before substituting the Gaussian
mixture derivatives. Positivity is required only at the point. -/
theorem log_density_second_derivative (p dp : ℝ → ℝ) (t ddp : ℝ)
    (hp : 0<p t) (h0 : HasDerivAt p (dp t) t) (h1 : HasDerivAt dp ddp t) :
    HasDerivAt (fun s => dp s/p s) (ddp/p t-(dp t)^2/(p t)^2) t := by
  convert h1.div h0 hp.ne' using 1 <;> field_simp <;> ring

/-- Substitution of the posterior first and second moments in the Hessian
of log p. The covariance term, including all off-diagonal entries, appears
from subtracting the square of the score. -/
theorem score_hessian_covariance (a v p xi xj mi mj mij δ : ℝ)
    (hv : v≠0) (hp : p≠0) :
    ((xi*xj-a*xi*mj-a*xj*mi+a^2*mij)/v^2-δ/v)*p/p-
      ((-(xi-a*mi)/v)*p)*((-(xj-a*mj)/v)*p)/p^2 =
      -δ/v+a^2/v^2*(mij-mi*mj) := by
  field_simp
  <;> ring

/-- Stationary standard Gaussian score gives zero probability-flow velocity
and the original OU drift for the reverse SDE. -/
theorem stationary_reverse_flow {E : Type*} [AddCommGroup E] [Module ℝ E] (x : E) :
    x+(2:ℝ) • (-x)= -x ∧ -x-(-x)=0 := by
  constructor
  · module
  · simp
end Asakura.Chapter9

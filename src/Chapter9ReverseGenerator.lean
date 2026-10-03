import FullAuditGaussianIBP
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

open Finset
open scoped BigOperators
namespace Asakura.Chapter9
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- Product expansion after the two integrations by parts. This includes
the divergence term d*f*p, which cancels against f*L*p. -/
theorem reverse_generator_product {d : ℕ} (p f : ℝ) (hp : p≠0)
    (y gradP gradF hessP hessF : Fin d → ℝ) :
    (Finset.sum Finset.univ (fun i : Fin d => (p*hessF i+2*gradF i*gradP i+f*hessP i)+(f*p+y i*(p*gradF i+f*gradP i))))-
      f*(Finset.sum Finset.univ (fun i : Fin d => hessP i+(p+y i*gradP i))) =
      p * Finset.sum Finset.univ (fun i : Fin d => hessF i + (y i + 2 * (gradP i / p)) * gradF i) := by
  simp only [mul_sum,←sum_sub_distrib]
  apply sum_congr rfl
  intro i _
  field_simp [hp]
  <;> ring

/-- The probability-flow continuity equation is the same forward equation,
with coefficient one rather than two in front of the score. -/
theorem probability_flow_divergence {d : ℕ} (p : ℝ) (hp : p≠0)
    (y gradP hessP : Fin d → ℝ) :
    -(Finset.sum Finset.univ (fun i : Fin d => (-1-(hessP i/p-(gradP i)^2/p^2))*p+(-y i-gradP i/p)*gradP i))=
      Finset.sum Finset.univ (fun i : Fin d => hessP i + p + y i * gradP i) := by
  rw [←sum_neg_distrib]
  apply sum_congr rfl
  intro i _
  field_simp [hp]
  <;> ring

/-- The coordinate and coordinate-product tests determine drift and
quadratic covariation of the reverse process. -/
theorem reverse_coordinate_tests (bi bj xi xj : ℝ) (same : Bool) :
    (bi*xj+bj*xi+(if same then 2 else 0))-xi*bj-xj*bi=
      (if same then 2 else 0) := by ring

/-- Reverse transition densities telescope to the forward joint density. -/
theorem reverse_density_telescope (p : ℕ → ℝ) (k : ℕ → ℝ)
    (hp : ∀ j,p j≠0) (n : ℕ) :
    p 0*(∏ j∈range n,p (j+1)*k j/p j)=p n*(∏ j∈range n,k j) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [prod_range_succ,prod_range_succ,←mul_assoc,ih]
    field_simp [hp n]
    <;> ring

/-- The density along a differentiable flow times its Jacobian is constant:
the continuity equation and Jacobi equation cancel exactly. -/
theorem transported_density_derivative (p J : ℝ → ℝ) (t c : ℝ)
    (hp : HasDerivAt p (-p t*c) t) (hJ : HasDerivAt J (c*J t) t) :
    HasDerivAt (fun s => p s*J s) 0 t := by
  convert hp.mul hJ using 1 <;> ring
end Asakura.Chapter9

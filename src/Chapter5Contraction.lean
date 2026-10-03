import Chapter5EnergyEstimates
import Mathlib.Topology.MetricSpace.Contracting

open Filter
open scoped Topology NNReal
namespace Asakura.Chapter5

/-- The Banach step with the *square* distance estimate printed in the book.
This theorem proves existence, uniqueness and convergence; constructing the
BSDE map and proving this estimate are distinct obligations. -/
theorem fixed_point_from_squared_estimate {E : Type*} [MetricSpace E]
    [CompleteSpace E] [Nonempty E] (F : E → E) (q : ℝ)
    (hq : 0 ≤ q) (hq1 : q < 1)
    (hF : ∀ x y, dist (F x) (F y)^2 ≤ q*dist x y^2) :
    ∃! x, F x = x := by
  let k : ℝ≥0 := ⟨Real.sqrt q,Real.sqrt_nonneg q⟩
  have hk : k < 1 := by
    change Real.sqrt q < 1
    nlinarith [Real.sq_sqrt hq,Real.sqrt_nonneg q]
  have hlip : LipschitzWith k F := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have hs := Real.sq_sqrt hq
    have hn : 0 ≤ Real.sqrt q*dist x y := mul_nonneg (Real.sqrt_nonneg _) dist_nonneg
    change dist (F x) (F y) ≤ Real.sqrt q*dist x y
    apply (sq_le_sq₀ dist_nonneg hn).1
    simpa only [mul_pow,hs] using hF x y
  have hc : ContractingWith k F := ⟨hk,hlip⟩
  refine ⟨hc.fixedPoint F,hc.fixedPoint_isFixedPt,?_⟩
  intro y hy
  exact hc.fixedPoint_unique hy

end Asakura.Chapter5

import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Ring

open MeasureTheory Matrix
open scoped BigOperators
namespace Asakura.Chapter10
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- The error second-moment matrix is positive semidefinite, including singular
initial covariance. No positivity of a Riccati solution is assumed here. -/
theorem error_covariance_positive {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) (e : ι → Ω → ℝ) (he : ∀ i,MemLp (e i) 2 P) :
    Matrix.PosSemidef (fun i j => ∫ w,e i w*e j w ∂P) := by
  classical
  have hi i j : Integrable (fun w => e i w*e j w) P := (he i).integrable_mul (he j)
  apply posSemidef_iff_dotProduct_mulVec.mpr
  constructor
  · ext i j
    simp only [conjTranspose_apply,star_trivial]
    congr 1
    funext w
    ring
  · intro x
    have hq : (∫ w,(∑ i,x i*e i w)^2 ∂P) =
        ∑ i,∑ j,x i*(∫ w,e i w*e j w ∂P)*x j := by
      simp only [pow_two,Finset.sum_mul_sum]
      rw [integral_finset_sum]
      · apply Finset.sum_congr rfl
        intro i _
        rw [integral_finset_sum]
        · apply Finset.sum_congr rfl
          intro j _
          have heq : (fun w => x i*e i w*(x j*e j w)) =
              (fun w => (x i*x j)*(e i w*e j w)) := by funext w; ring
          rw [heq,integral_const_mul]
          ring
        · intro j _
          convert (hi i j).const_mul (x i*x j) using 1
          funext w
          ring
      · intro i _
        apply integrable_finset_sum
        intro j _
        convert (hi i j).const_mul (x i*x j) using 1
        funext w
        ring
    have hn : 0≤(∫ w,(∑ i,x i*e i w)^2 ∂P) :=
      integral_nonneg (fun w => sq_nonneg _)
    rw [hq] at hn
    simpa only [dotProduct,mulVec,Pi.star_apply,star_trivial,Finset.mul_sum,mul_assoc] using hn

end Asakura.Chapter10

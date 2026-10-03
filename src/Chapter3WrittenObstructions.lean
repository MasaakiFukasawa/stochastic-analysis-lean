import Chapter3WrittenLimits
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

open MeasureTheory Set
open scoped Topology
namespace Asakura.Chapter3Written

/-- Coarsening a partition can strictly reduce its variation sum: values
0,1,0 give fine sum 2 but endpoint sum 0. -/
theorem variation_partition_equality_false :
    |(0 : ℝ)-0| < |(1 : ℝ)-0| + |(0 : ℝ)-1| := by norm_num

/-- Omitting the lower endpoint term in the BDG integral creates a strict
inequality: p=1, alpha=1, alpha+X*=4 gives 2+(2-1)=3, not 4. -/
theorem bdg_lower_endpoint_equality_false :
    (2 : ℝ) + (1-(1:ℝ)/2) * (2/(1:ℝ)) * (2-1) < (2/(1:ℝ))*2 := by norm_num

/-- At zero the reciprocal-power cancellation in the p<2 proof is false;
with Lean's totalized real powers and p=1 its product is zero, not one. -/
theorem singular_inverse_cancellation_at_zero :
    (0 : ℝ)^((2-1:ℝ)/4) * (0 : ℝ)^((1-2:ℝ)/4) ≠ 1 := by norm_num

end Asakura.Chapter3Written

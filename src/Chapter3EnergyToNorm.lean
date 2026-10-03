import Chapter3EnergyBounds

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter3Complete
open Asakura.Chapter2Complete

/-- Recover the L2 bound from the second moment, also when C=0. -/
theorem l2_bound_of_square_integral_le
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (f : Ω → ℝ) (hf : MemLp f 2 P) (C : ℝ) (hC : 0 ≤ C)
    (hb : (∫ ω, f ω^2 ∂P) ≤ C^2) :
    eLpNorm f 2 P ≤ ENNReal.ofReal C := by
  rw [real_eLpNorm_two_energy P f hf,
    ENNReal.ofReal_rpow_of_nonneg (integral_nonneg fun ω => sq_nonneg _) (by norm_num)]
  apply ENNReal.ofReal_le_ofReal
  rw [← Real.sqrt_eq_rpow]
  exact (Real.sqrt_le_sqrt hb).trans_eq (Real.sqrt_sq hC)

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.l2_bound_of_square_integral_le

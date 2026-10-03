import Chapter3WrittenLimits
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter3Complete

/-- Summable L2 path errors give almost sure convergence in the path norm,
without passage to a subsequence. This applies to the actual continuous
path-valued errors in the discrete approximation. -/
theorem ae_zero_of_summable_l2_errors
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    (P : Measure Ω) [IsProbabilityMeasure P] (Z : ℕ → Ω → E)
    (hZ : ∀ n, AEStronglyMeasurable (Z n) P)
    (hs : (∑' n, eLpNorm (Z n) 2 P) ≠ ∞) :
    ∀ᵐ ω ∂P, Tendsto (fun n => Z n ω) atTop (𝓝 0) := by
  have hb (n) : (∫⁻ ω, ‖Z n ω‖ₑ ∂P) ≤ eLpNorm (Z n) 2 P := by
    rw [← eLpNorm_one_eq_lintegral_enorm (hZ n)]
    exact eLpNorm_le_eLpNorm_of_exponent_le (by norm_num)
  have hsum : (∫⁻ ω, ∑' n, ‖Z n ω‖ₑ ∂P) ≠ ∞ := by
    rw [lintegral_tsum (fun n => (hZ n).enorm)]
    exact ne_of_lt ((ENNReal.tsum_le_tsum hb).trans_lt (lt_top_iff_ne_top.mpr hs))
  filter_upwards [ae_lt_top' (AEMeasurable.tsum fun n => (hZ n).enorm) hsum] with ω hω
  have hs' : Summable (fun n => (‖Z n ω‖₊ : ℝ)) := by
    rw [← ENNReal.tsum_coe_ne_top_iff_summable_coe]
    exact hω.ne
  exact tendsto_zero_iff_norm_tendsto_zero.mpr hs'.tendsto_atTop_zero

/-- In particular the dyadic rate in the manuscript is summable in L2. -/
theorem ae_zero_of_dyadic_l2_errors
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    (P : Measure Ω) [IsProbabilityMeasure P] (Z : ℕ → Ω → E)
    (hZ : ∀ n, AEStronglyMeasurable (Z n) P) (B : ℝ)
    (hb : ∀ n, eLpNorm (Z n) 2 P ≤ ENNReal.ofReal (B*(1/2:ℝ)^n)) :
    ∀ᵐ ω ∂P, Tendsto (fun n => Z n ω) atTop (𝓝 0) := by
  apply ae_zero_of_summable_l2_errors P Z hZ
  have hs : Summable (fun n : ℕ => B*(1/2:ℝ)^n) :=
    (summable_geometric_of_norm_lt_one (by norm_num : ‖(1/2:ℝ)‖ < 1)).mul_left B
  exact ne_of_lt ((ENNReal.tsum_le_tsum hb).trans_lt hs.tsum_ofReal_lt_top)

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.ae_zero_of_summable_l2_errors

#print axioms Asakura.Chapter3Complete.ae_zero_of_dyadic_l2_errors

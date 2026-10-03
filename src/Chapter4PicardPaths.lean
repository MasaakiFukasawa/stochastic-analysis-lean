import Chapter4Picard
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Topology.ContinuousMap.Bounded.Normed

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter4

/-- The Tonelli step behind the manuscript's almost surely absolutely
uniformly convergent Picard series. With E=C([0,T],R^d), the norm here is
precisely the path supremum norm. -/
theorem picard_path_series {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [CompleteSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P] (Z : ℕ → Ω → E)
    (hZ : ∀ n, AEStronglyMeasurable (Z n) P)
    (A a : ℝ) (ha : 0 ≤ a)
    (hb : ∀ n, eLpNorm (Z n) 2 P ≤
      ENNReal.ofReal (A * Real.sqrt (a^n/(n.factorial:ℝ)))) :
    ∀ᵐ ω ∂P, Summable (fun n => ‖Z n ω‖) ∧ Summable (fun n => Z n ω) := by
  have hs : Summable (fun n => A * Real.sqrt (a^n/(n.factorial:ℝ))) :=
    (summable_sqrt_factorial a ha).mul_left A
  have hnorm (n) : (∫⁻ ω, ‖Z n ω‖ₑ ∂P) ≤ eLpNorm (Z n) 2 P := by
    rw [← eLpNorm_one_eq_lintegral_enorm (hZ n)]
    exact eLpNorm_le_eLpNorm_of_exponent_le (by norm_num)
  have hi : (∫⁻ ω, ∑' n, ‖Z n ω‖ₑ ∂P) < ∞ := by
    rw [lintegral_tsum (fun n => (hZ n).enorm)]
    exact (ENNReal.tsum_le_tsum (fun n => (hnorm n).trans (hb n))).trans_lt hs.tsum_ofReal_lt_top
  filter_upwards [ae_lt_top' (AEMeasurable.tsum fun n => (hZ n).enorm) hi.ne] with ω hω
  have hn : Summable (fun n => ‖Z n ω‖) := by
    change Summable (fun n => (‖Z n ω‖₊ : ℝ))
    rw [← ENNReal.tsum_coe_ne_top_iff_summable_coe]
    exact hω.ne
  exact ⟨hn,hn.of_norm⟩

end Asakura.Chapter4

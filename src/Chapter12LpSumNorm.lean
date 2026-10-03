import Chapter12LpNormLift
import Mathlib.Analysis.Normed.Lp.PiLp

open MeasureTheory
open scoped ENNReal
namespace Asakura.Chapter12

noncomputable def lpSumNorm {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    {E : I → Type*} [∀i,NormedAddCommGroup (E i)]
    {P : Measure Ω} {p : ℝ≥0∞} [Fact (1≤p)]
    (f : ∀i,Lp (E i) p P) : Lp ℝ p P := ∑i,lpNormLift (f i)

theorem lpSumNorm_coe {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    {E : I → Type*} [∀i,NormedAddCommGroup (E i)]
    {P : Measure Ω} {p : ℝ≥0∞} [Fact (1≤p)]
    (f : ∀i,Lp (E i) p P) :
    (lpSumNorm f : Ω → ℝ)=ᵐ[P] (fun w => ∑i,‖f i w‖) := by
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ (fun i => lpNormLift (f i)),
    ae_all_iff.mpr (fun i => lpNormLift_coe (f i))] with w hw hi
  change (∑i,lpNormLift (f i)) w=∑i,‖f i w‖
  rw [hw]
  exact Finset.sum_congr rfl (fun i _ => hi i)

theorem lpSumNorm_norm_le {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    {E : I → Type*} [∀i,NormedAddCommGroup (E i)]
    {P : Measure Ω} {p : ℝ≥0∞} [Fact (1≤p)]
    (f : ∀i,Lp (E i) p P) : ‖lpSumNorm f‖≤‖WithLp.toLp 1 f‖ := by
  rw [PiLp.norm_eq_of_L1]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => lpNormLift_norm_le (f i)))
end Asakura.Chapter12
#print axioms Asakura.Chapter12.lpSumNorm_norm_le

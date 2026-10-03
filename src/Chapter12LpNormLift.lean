import Chapter12LpAffineNormBound

open MeasureTheory
open scoped ENNReal
namespace Asakura.Chapter12

noncomputable def lpNormLift {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    {P : Measure Ω} {p : ℝ≥0∞} (f : Lp E p P) : Lp ℝ p P :=
  (Lp.memLp f).norm.toLp (fun w => ‖f w‖)

theorem lpNormLift_coe {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    {P : Measure Ω} {p : ℝ≥0∞} (f : Lp E p P) :
    (lpNormLift f : Ω → ℝ)=ᵐ[P] (fun w => ‖f w‖) := (Lp.memLp f).norm.coeFn_toLp

theorem lpNormLift_norm_le {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    {P : Measure Ω} {p : ℝ≥0∞} (f : Lp E p P) : ‖lpNormLift f‖≤‖f‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [lpNormLift_coe f] with w hw
  rw [hw,norm_norm]
end Asakura.Chapter12
#print axioms Asakura.Chapter12.lpNormLift_norm_le

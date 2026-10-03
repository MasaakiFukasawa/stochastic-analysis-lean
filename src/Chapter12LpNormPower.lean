import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.Holder

open MeasureTheory
open scoped ENNReal
namespace Asakura.Chapter12
set_option maxHeartbeats 1800000

theorem lp_norm_power {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    (P : Measure Ω) (p : ℝ≥0∞) (n : ℕ) (hn : 0<n)
    (f : Ω → E) (hf : MemLp f (p*n) P)
    (hg : MemLp (fun w => ‖f w‖^n) p P) :
    ‖hg.toLp (fun w => ‖f w‖^n)‖=‖hf.toLp f‖^n := by
  rw [Lp.norm_toLp,Lp.norm_toLp]
  have he := eLpNorm_norm_rpow (p:=p) f hf.aestronglyMeasurable (by exact_mod_cast hn : (0:ℝ)<n)
  simp only [Real.rpow_natCast,ENNReal.ofReal_natCast,ENNReal.rpow_natCast] at he
  rw [he,ENNReal.toReal_pow]
end Asakura.Chapter12
#print axioms Asakura.Chapter12.lp_norm_power

import Chapter12LpNormPower

open MeasureTheory
open scoped ENNReal
namespace Asakura.Chapter12

theorem memLp_norm_power {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    (P : Measure Ω) (p : ℝ≥0∞) (n : ℕ) (hn : 0<n)
    (f : Ω → E) (hf : MemLp f (p*n) P) : MemLp (fun w => ‖f w‖^n) p P := by
  have h := hf.norm_rpow_div (n:ℝ≥0∞)
  have hn0 : (n:ℝ≥0∞)≠0 := by exact_mod_cast hn.ne'
  simpa only [ENNReal.toReal_natCast,Real.rpow_natCast,
    ENNReal.mul_div_cancel_right hn0 (ENNReal.natCast_ne_top n)] using h

noncomputable def lpNormPower {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    {P : Measure Ω} {p : ℝ≥0∞} (n : ℕ) (hn : 0<n) (f : Lp E (p*n) P) : Lp ℝ p P :=
  (memLp_norm_power P p n hn f (Lp.memLp f)).toLp (fun w => ‖f w‖^n)

theorem lpNormPower_coe {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    {P : Measure Ω} {p : ℝ≥0∞} (n : ℕ) (hn : 0<n) (f : Lp E (p*n) P) :
    (lpNormPower n hn f : Ω → ℝ)=ᵐ[P] (fun w => ‖f w‖^n) :=
  (memLp_norm_power P p n hn f (Lp.memLp f)).coeFn_toLp

theorem lpNormPower_norm {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    {P : Measure Ω} {p : ℝ≥0∞} (n : ℕ) (hn : 0<n) (f : Lp E (p*n) P) :
    ‖lpNormPower n hn f‖=‖f‖^n := by
  rw [lpNormPower,lp_norm_power P p n hn f (Lp.memLp f)]
  congr 1
  congr 1
  exact Lp.ext (Lp.memLp f).coeFn_toLp
end Asakura.Chapter12
#print axioms Asakura.Chapter12.lpNormPower_norm

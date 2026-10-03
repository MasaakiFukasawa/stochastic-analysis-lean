import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

open MeasureTheory
open scoped ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false

/-- The continuous inclusion Lq into Lp on a probability space. It keeps
the same random variable and is used to compare closed Sobolev derivatives
constructed with different exponents. -/
noncomputable def probabilityLpInclusion {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)] (hpq : p ≤ q) :
    Lp E q P →L[ℝ] Lp E p P := by
  let J := fun f : Lp E q P => ((Lp.memLp f).mono_exponent hpq).toLp f
  have hj (f : Lp E q P) : (J f : Ω → E) =ᵐ[P] (f : Ω → E) :=
    ((Lp.memLp f).mono_exponent hpq).coeFn_toLp
  let L : Lp E q P →ₗ[ℝ] Lp E p P :=
    { toFun := J
      map_add' := by
        intro f g
        apply Lp.ext
        filter_upwards [hj (f+g),hj f,hj g,Lp.coeFn_add f g,Lp.coeFn_add (J f) (J g)] with w h1 h2 h3 h4 h5
        rw [h1,h4,h5,Pi.add_apply,Pi.add_apply,h2,h3]
      map_smul' := by
        intro a f
        apply Lp.ext
        filter_upwards [hj (a • f),hj f,Lp.coeFn_smul a f,Lp.coeFn_smul a (J f)] with w h1 h2 h3 h4
        change J (a • f) w = (a • J f) w
        rw [h1,h3,h4,Pi.smul_apply,Pi.smul_apply,h2] }
  apply L.mkContinuous 1
  intro f
  change ‖J f‖ ≤ 1*‖f‖
  rw [one_mul,Lp.norm_def,Lp.norm_def,eLpNorm_congr_ae (hj f)]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f) (eLpNorm_le_eLpNorm_of_exponent_le hpq)

theorem probabilityLpInclusion_coe {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)] (hpq : p ≤ q) (f : Lp E q P) :
    (probabilityLpInclusion P p q hpq f : Ω → E) =ᵐ[P] (f : Ω → E) :=
  ((Lp.memLp f).mono_exponent hpq).coeFn_toLp

end Asakura.Chapter12

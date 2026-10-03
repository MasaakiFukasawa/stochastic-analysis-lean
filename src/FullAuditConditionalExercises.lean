import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.Tactic.Linarith

open MeasureTheory Set Filter
namespace Asakura.FullAudit

/-- Exercise 1.1.6(1), with the essential bound written explicitly. -/
theorem exercise_ce_bounded_pullout {Ω : Type*} {m m0 : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (hm : m ≤ m0)
    {X Y : Ω → ℝ} (hX : Integrable X P) (hY : AEStronglyMeasurable[m] Y P)
    (C : ℝ) (hbound : ∀ᵐ ω ∂P, ‖Y ω‖ ≤ C) :
    P[Y * X | m] =ᵐ[P] Y * P[X | m] :=
  condExp_stronglyMeasurable_mul_of_bound₀ hm hY hX C hbound

/-- Exercise 1.1.6(2), C5 for integrable random variables. -/
theorem exercise_ce_nested {Ω : Type*} {h m m0 : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (hh : h ≤ m) (hm : m ≤ m0)
    (X : Ω → ℝ) : P[P[X | m] | h] =ᵐ[P] P[X | h] :=
  condExp_condExp_of_le hh hm

/-- Exercise 1.1.6(3). -/
theorem exercise_ce_monotone {Ω : Type*} {m m0 : MeasurableSpace Ω}
    (P : Measure Ω) {X Y : Ω → ℝ} (hX : Integrable X P)
    (hY : Integrable Y P) (hXY : X ≤ᵐ[P] Y) :
    P[X | m] ≤ᵐ[P] P[Y | m] := condExp_mono hX hY hXY

/-- Exercise 1.1.6(4): test the nonpositive set and use the zero-integral criterion.
No strict-positivity theorem for conditional expectation is assumed. -/
theorem exercise_ce_strictly_positive {Ω : Type*} {m m0 : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (hm : m ≤ m0)
    {X : Ω → ℝ} (hX : Integrable X P) (hpos : ∀ᵐ ω ∂P, 0 < X ω) :
    ∀ᵐ ω ∂P, 0 < (P[X | m]) ω := by
  let Y := P[X | m]
  let A := {ω | Y ω ≤ 0}
  have hA : MeasurableSet[m] A :=
    measurableSet_le stronglyMeasurable_condExp.measurable measurable_const
  have hYnonneg : ∀ᵐ ω ∂P, 0 ≤ Y ω := condExp_nonneg (hpos.mono fun _ h => h.le)
  have hYzero : ∀ᵐ ω ∂P.restrict A, Y ω = 0 := by
    rw [ae_restrict_iff' (hm _ hA)]
    filter_upwards [hYnonneg] with ω hω hωA
    exact le_antisymm hωA hω
  have hzero : ∫ ω in A, X ω ∂P = 0 := by
    rw [← setIntegral_condExp hm hX hA]
    exact integral_eq_zero_of_ae hYzero
  have hXzero : ∀ᵐ ω ∂P.restrict A, X ω = 0 :=
    (integral_eq_zero_iff_of_nonneg_ae
      ((ae_restrict_of_ae hpos).mono fun _ h => h.le) hX.integrableOn).mp hzero
  have houtside : ∀ᵐ ω ∂P, ω ∉ A := by
    rw [ae_restrict_iff' (hm _ hA)] at hXzero
    filter_upwards [hXzero, hpos] with ω hω hωpos
    intro hωA
    exact (ne_of_gt hωpos) (hω hωA)
  exact houtside.mono fun _ h => lt_of_not_ge h

/-- Exercise 1.2.1: Holder supplies integrability of the product, then pull out Y. -/
theorem exercise_ce_holder_pullout {Ω : Type*} {m m0 : MeasurableSpace Ω}
    (P : Measure Ω) [IsFiniteMeasure P] {p q : ENNReal}
    [p.HolderConjugate q] {X Y : Ω → ℝ}
    (hX : MemLp X p P) (hY : MemLp Y q P)
    (hYm : AEStronglyMeasurable[m] Y P) :
    P[X * Y | m] =ᵐ[P] P[X | m] * Y := by
  apply condExp_mul_of_aestronglyMeasurable_right hYm _ (hX.integrable (ENNReal.HolderConjugate.one_le p q))
  exact hX.integrable_mul hY

end Asakura.FullAudit

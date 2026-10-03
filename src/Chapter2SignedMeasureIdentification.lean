import Chapter2CovarianceAbsoluteContinuity
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

open MeasureTheory Set
namespace Asakura.Chapter2Complete
open Asakura.FullAudit
set_option maxHeartbeats 900000

/-- Interval increments determine the actual finite signed measure. -/
theorem signed_measure_ext_Ioc (ν κ : SignedMeasure ℝ)
    (h : ∀ a b, a < b → ν (Ioc a b) = κ (Ioc a b)) : ν = κ := by
  have he : ν.toJordanDecomposition.posPart + κ.toJordanDecomposition.negPart =
      κ.toJordanDecomposition.posPart + ν.toJordanDecomposition.negPart := by
    apply Measure.ext_of_Ioc
    intro a b hab
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    change (ν.toJordanDecomposition.posPart + κ.toJordanDecomposition.negPart).real (Ioc a b) =
      (κ.toJordanDecomposition.posPart + ν.toJordanDecomposition.negPart).real (Ioc a b)
    rw [measureReal_add_apply, measureReal_add_apply]
    have hh := h a b hab
    rw [ν.apply_eq_posPart_real_sub_negPart_real measurableSet_Ioc,
      κ.apply_eq_posPart_real_sub_negPart_real measurableSet_Ioc] at hh
    linarith
  ext s hs
  have hh := congrArg (fun μ : Measure ℝ => μ.real s) he
  rw [measureReal_add_apply, measureReal_add_apply] at hh
  rw [ν.apply_eq_posPart_real_sub_negPart_real hs,
    κ.apply_eq_posPart_real_sub_negPart_real hs]
  linarith

/-- Clipping the left half-line is legitimate because its total variation is zero. -/
theorem signed_measure_Ioc_clip_zero (ν : SignedMeasure ℝ)
    (hzero : ν.totalVariation (Iic 0) = 0) (a b : ℝ) :
    ν (Ioc a b) = ν (Ioc (max 0 a) (max 0 b)) := by
  rw [← signedIntegralRaw_indicator ν _ measurableSet_Ioc,
    ← signedIntegralRaw_indicator ν _ measurableSet_Ioc]
  apply signed_integral_congr_of_absolute_continuity ν.totalVariation ν (by rfl)
  have hp : ∀ᵐ r ∂ν.totalVariation, 0 < r := by
    rw [ae_iff]
    change ν.totalVariation {r | ¬0 < r} = 0
    simp only [not_lt]
    exact hzero
  filter_upwards [hp] with r hr
  have he : r ∈ Ioc a b ↔ r ∈ Ioc (max 0 a) (max 0 b) := by
    simp only [mem_Ioc, max_lt_iff, le_max_iff]
    constructor
    · intro h; exact ⟨⟨hr,h.1⟩,Or.inr h.2⟩
    · rintro ⟨h,hb | hb⟩
      · exact False.elim (not_le_of_gt hr hb)
      · exact ⟨h.2,hb⟩
  simp only [indicator_apply,he]

/-- Positive-time increments and absence of mass at nonpositive times suffice.
This is the identification needed for covariance measures on finite horizons. -/
theorem signed_measure_ext_positive_Ioc (ν κ : SignedMeasure ℝ)
    (hν : ν.totalVariation (Iic 0) = 0) (hκ : κ.totalVariation (Iic 0) = 0)
    (h : ∀ a b, 0 ≤ a → a ≤ b → ν (Ioc a b) = κ (Ioc a b)) : ν = κ := by
  apply signed_measure_ext_Ioc
  intro a b hab
  rw [signed_measure_Ioc_clip_zero ν hν, signed_measure_Ioc_clip_zero κ hκ]
  exact h _ _ (le_max_left _ _) (max_le_max_left _ hab.le)

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.signed_measure_ext_positive_Ioc

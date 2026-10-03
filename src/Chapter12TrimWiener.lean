import Chapter12WienerCylinder
import Mathlib.MeasureTheory.Function.ConditionalExpectation.AEMeasurable

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

/-- Restriction to a smaller information space preserves the Wiener
isometry when all its values are measurable for that information. -/
theorem wiener_isometry_on_trim {Ω H : Type*} {m : MeasurableSpace Ω}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (mT : MeasurableSpace Ω) (hle : mT ≤ m)
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P)
    (hmeas : ∀ h, AEStronglyMeasurable[mT] (W h : Ω → ℝ) P)
    (hG : ∀ h, HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P) :
    ∃ V : H →ₗᵢ[ℝ] Lp ℝ 2 (P.trim hle),
      (∀ h, (V h : Ω → ℝ) =ᵐ[P] (W h : Ω → ℝ)) ∧
      (∀ h, HasLaw (V h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) (P.trim hle)) := by
  letI : MeasurableSpace Ω := m
  let J : H →ₗᵢ[ℝ] lpMeas ℝ ℝ mT 2 P :=
    { toLinearMap :=
        { toFun := fun h => ⟨W h, (mem_lpMeas_iff_aestronglyMeasurable).mpr (hmeas h)⟩
          map_add' := fun x y => Subtype.ext (W.map_add x y)
          map_smul' := fun a x => Subtype.ext (W.map_smul a x) }
      norm_map' := fun h => W.norm_map h }
  let V := (lpMeasToLpTrimLie ℝ ℝ 2 P hle).toLinearIsometry.comp J
  have he (h : H) : (V h : Ω → ℝ) =ᵐ[P] (W h : Ω → ℝ) :=
    lpMeasToLpTrim_ae_eq hle (J h)
  refine ⟨V,he,fun h => ?_⟩
  have hm : Measurable[mT] (V h : Ω → ℝ) := (Lp.stronglyMeasurable (V h)).measurable
  have hmap : @Measure.map Ω ℝ mT _ (V h) (P.trim hle) = P.map (V h) := by
    ext s hs
    rw [Measure.map_apply hm hs,Measure.map_apply (hm.mono hle le_rfl) hs,
      trim_measurableSet_eq hle (hm hs)]
  refine ⟨hm.aemeasurable,?_⟩
  rw [hmap]
  exact (Measure.map_congr (he h)).trans (hG h).map_eq

end Asakura.Chapter12

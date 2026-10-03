import Chapter2SignedDifferenceIntegral
import Chapter2VariationIntegralFormula

open MeasureTheory Set Filter
open scoped ENNReal
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

theorem signed_sum_integral {S : Type*} [MeasurableSpace S]
    (ν κ : SignedMeasure S) (f : S → ℝ)
    (hn : Integrable f ν.totalVariation) (hk : Integrable f κ.totalVariation) :
    signedIntegralRaw (ν+κ) f=signedIntegralRaw ν f+signedIntegralRaw κ f := by
  let α := ν.toJordanDecomposition.posPart+κ.toJordanDecomposition.posPart
  let β := ν.toJordanDecomposition.negPart+κ.toJordanDecomposition.negPart
  have hnp := hn.mono_measure (show ν.toJordanDecomposition.posPart≤ν.totalVariation from fun A => le_add_right le_rfl)
  have hnn := hn.mono_measure (show ν.toJordanDecomposition.negPart≤ν.totalVariation from fun A => le_add_left le_rfl)
  have hkp := hk.mono_measure (show κ.toJordanDecomposition.posPart≤κ.totalVariation from fun A => le_add_right le_rfl)
  have hkn := hk.mono_measure (show κ.toJordanDecomposition.negPart≤κ.totalVariation from fun A => le_add_left le_rfl)
  have hi : Integrable f (α+β) := integrable_add_measure.mpr ⟨integrable_add_measure.mpr ⟨hnp,hkp⟩,integrable_add_measure.mpr ⟨hnn,hkn⟩⟩
  have he : α.toSignedMeasure-β.toSignedMeasure=ν+κ := by
    dsimp only [α,β]
    rw [Measure.toSignedMeasure_add,Measure.toSignedMeasure_add]
    calc
      _ = (ν.toJordanDecomposition.posPart.toSignedMeasure-ν.toJordanDecomposition.negPart.toSignedMeasure)+
          (κ.toJordanDecomposition.posPart.toSignedMeasure-κ.toJordanDecomposition.negPart.toSignedMeasure) := by abel
      _ = ν+κ := by rw [←JordanDecomposition.toSignedMeasure,←JordanDecomposition.toSignedMeasure,
        SignedMeasure.toSignedMeasure_toJordanDecomposition,SignedMeasure.toSignedMeasure_toJordanDecomposition]
  rw [←he,signed_difference_integral α β f hi]
  dsimp only [α,β,signedIntegralRaw]
  rw [integral_add_measure hnp hkp,integral_add_measure hnn hkn]
  ring

theorem signed_sum_variation_le {S : Type*} [MeasurableSpace S] (ν κ : SignedMeasure S) :
    (ν+κ).totalVariation≤ν.totalVariation+κ.totalVariation := by
  simp only [SignedMeasure.totalVariation_eq_variation]
  exact VectorMeasure.variation_add_le

/-- Additivity in the finite-variation integrator, from its actual signed
increments and decomposition-independent signed integration. -/
theorem variation_integrator_add {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {T : EReal} [Fact (0≤T)] (c : ℕ → ℝ) (hc : ∀ n,0≤c n)
    (A B I J : ClosedTime T → Ω → ℝ) (H : Ω × ℝ → ℝ)
    (hI : VariationIntegralFormula P c hc A H I)
    (hJ : VariationIntegralFormula P c hc B H J) :
    VariationIntegralFormula P c hc (fun t w => A t w+B t w) H (fun t w => I t w+J t w) := by
  intro n
  obtain ⟨ν,hsν,hν,hi,hform⟩ := hI n
  obtain ⟨κ,hsκ,hκ,hj,hformJ⟩ := hJ n
  refine ⟨fun w => ν w+κ w,?_,?_,?_,?_⟩
  · filter_upwards [hsν,hsκ] with w hn hk
    exact ae_mono (signed_sum_variation_le (ν w) (κ w)) (ae_add_measure_iff.mpr ⟨hn,hk⟩)
  · filter_upwards [hν,hκ] with w hn hk
    intro s t hst
    rw [VectorMeasure.add_apply,hn s t hst,hk s t hst]
    ring
  · filter_upwards [hi,hj] with w hn hk
    exact (integrable_add_measure.mpr ⟨hn,hk⟩).mono_measure (signed_sum_variation_le (ν w) (κ w))
  · filter_upwards [hi,hj,hform,hformJ] with w hn hk hf hg
    intro t
    rw [hf t,hg t]
    unfold signedCumulative
    exact (signed_sum_integral (ν w) (κ w) _ (hn.indicator measurableSet_Iic) (hk.indicator measurableSet_Iic)).symm

end Asakura.Chapter11

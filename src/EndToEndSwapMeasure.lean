import EndToEndBondAnnuity

open MeasureTheory Set
open scoped NNReal
namespace Asakura.EndToEnd.BondMarket
open Asakura.Chapter13
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]

noncomputable def swapMeasure (M : BondMarket Q) {J : Type*} [Fintype J]
    (a : J → ℝ) (u : J → ℝ≥0) (S : ℝ≥0) : Measure Ω :=
  Q.withDensity (fun ω => ENNReal.ofReal
    ((M.annuity a u S ω / M.bank S ω) /
      (∫ ω, M.annuity a u S ω / M.bank S ω ∂Q)))

theorem swap_numeraire (M : BondMarket Q) {J : Type*} [Fintype J] [Nonempty J]
    (a : J → ℝ) (ha : ∀ j, 0 < a j) (u : J → ℝ≥0) (S : ℝ≥0)
    (X : ℝ≥0 → Ω → ℝ) (hXm : ∀ t, Measurable[M.F t] (X t))
    (hXi : ∀ t, Integrable (fun ω => X t ω / M.bank t ω) Q)
    (hX : ∀ s t, s ≤ t → Q[(fun ω => X t ω / M.bank t ω)|M.F s] =ᵐ[Q]
      (fun ω => X s ω / M.bank s ω)) :
    IsProbabilityMeasure (M.swapMeasure a u S) ∧
    (∀ t : Iic S, Integrable (fun ω => X t ω / M.annuity a u t ω) (M.swapMeasure a u S)) ∧
    (∀ s t : Iic S, s ≤ t →
      (M.swapMeasure a u S)[(fun ω => X t ω / M.annuity a u t ω)|M.F s]
        =ᵐ[M.swapMeasure a u S] (fun ω => X s ω / M.annuity a u s ω)) := by
  obtain ⟨hAm,hAi,hA⟩ := M.annuity_discounted a u
  apply bond_numeraire_martingale Q (fun t : Iic S => M.F t)
    (fun s t hst => M.mono hst) (fun t => M.le t)
    (fun ω => M.annuity a u S ω / M.bank S ω)
    (((hAm S).div (M.bank_adapted S)).mono (M.le S) le_rfl)
    (hAi S)
  · exact (M.annuity_positive_ae a ha u S).mono (fun ω hω => div_pos hω (M.bank_pos S ω))
  · exact fun t ω => M.bank_pos t ω |>.ne'
  · exact fun t => ((hAm t).div (M.bank_adapted t)).stronglyMeasurable
  · exact fun t => hA t S t.property
  · exact fun t => ((hXm t).div (M.bank_adapted t)).stronglyMeasurable
  · exact fun t => hXi t
  · exact fun s t hst => hX s t hst

#print axioms swap_numeraire
end Asakura.EndToEnd.BondMarket

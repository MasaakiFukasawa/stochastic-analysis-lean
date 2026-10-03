import Chapter13BondNumeraire
import Chapter13ClosedBondPricing

open MeasureTheory Set
open scoped NNReal
namespace Asakura.EndToEnd
open Asakura.Chapter13
set_option backward.isDefEq.respectTransparency false

/-- The bond-pricing assumptions, before any short-rate or HJM specialization.
The conditional pricing formula is a theorem of this structure, not a field. -/
structure BondMarket {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q] where
  F : ℝ≥0 → MeasurableSpace Ω
  mono : Monotone F
  le : ∀ t, F t ≤ ‹MeasurableSpace Ω›
  bank : ℝ≥0 → Ω → ℝ
  bank_pos : ∀ t ω, 0 < bank t ω
  bank_adapted : ∀ t, Measurable[F t] (bank t)
  bond : ℝ≥0 → ℝ≥0 → Ω → ℝ
  bond_adapted : ∀ u t, Measurable[F t] (bond u t)
  after_maturity : ∀ u t, u ≤ t → ∀ ω, bond u t ω = bank t ω / bank u ω
  discounted_integrable : ∀ u t, Integrable (fun ω => bond u t ω / bank t ω) Q
  discounted_martingale : ∀ u s t, s ≤ t →
    Q[(fun ω => bond u t ω / bank t ω)|F s] =ᵐ[Q]
      (fun ω => bond u s ω / bank s ω)

namespace BondMarket
variable {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]

theorem terminal_discount_integrable (M : BondMarket Q) (u : ℝ≥0) :
    Integrable (fun ω => (M.bank u ω)⁻¹) Q := by
  convert M.discounted_integrable u u using 1
  funext ω
  rw [M.after_maturity u u le_rfl ω, div_self (ne_of_gt (M.bank_pos u ω)), one_div]

theorem discounted_conditional (M : BondMarket Q) (u t : ℝ≥0) :
    Q[(fun ω => (M.bank u ω)⁻¹)|M.F t] =ᵐ[Q]
      (fun ω => M.bond u t ω / M.bank t ω) := by
  have hterminal : (fun ω => M.bond u u ω / M.bank u ω) =
      (fun ω => (M.bank u ω)⁻¹) := by
    funext ω
    rw [M.after_maturity u u le_rfl ω, div_self (ne_of_gt (M.bank_pos u ω)), one_div]
  have h := frozen_terminal_conditional Q M.F M.mono M.le
    (fun s ω => M.bond u s ω / M.bank s ω)
    (fun s => ((M.bond_adapted u s).div (M.bank_adapted s)).stronglyMeasurable)
    (M.discounted_integrable u) (M.discounted_martingale u) u (by
      intro s hs
      apply Filter.Eventually.of_forall
      intro ω
      dsimp only
      rw [M.after_maturity u s hs ω, M.after_maturity u u le_rfl ω]
      field_simp [ne_of_gt (M.bank_pos s ω), ne_of_gt (M.bank_pos u ω)]) t
  rwa [hterminal] at h

theorem pricing (M : BondMarket Q) (u t : ℝ≥0) :
    M.bond u t =ᵐ[Q]
      (fun ω => M.bank t ω * Q[(fun ω => (M.bank u ω)⁻¹)|M.F t] ω) := by
  filter_upwards [M.discounted_conditional u t] with ω hω
  rw [hω]
  field_simp [ne_of_gt (M.bank_pos t ω)]

noncomputable def forwardMeasure (M : BondMarket Q) (u : ℝ≥0) : Measure Ω :=
  Q.withDensity (fun ω => ENNReal.ofReal
    ((M.bank u ω)⁻¹ / (∫ ω, (M.bank u ω)⁻¹ ∂Q)))

theorem forward_numeraire (M : BondMarket Q) (u : ℝ≥0)
    (X : ℝ≥0 → Ω → ℝ) (hXm : ∀ t, Measurable[M.F t] (X t))
    (hXi : ∀ t, Integrable (fun ω => X t ω / M.bank t ω) Q)
    (hX : ∀ s t, s ≤ t → Q[(fun ω => X t ω / M.bank t ω)|M.F s] =ᵐ[Q]
      (fun ω => X s ω / M.bank s ω)) :
    IsProbabilityMeasure (M.forwardMeasure u) ∧
    (∀ t, Integrable (fun ω => X t ω / M.bond u t ω) (M.forwardMeasure u)) ∧
    (∀ s t, s ≤ t → (M.forwardMeasure u)[(fun ω => X t ω / M.bond u t ω)|M.F s]
      =ᵐ[M.forwardMeasure u] (fun ω => X s ω / M.bond u s ω)) := by
  exact bond_numeraire_martingale Q M.F M.mono M.le
    (fun ω => (M.bank u ω)⁻¹) ((M.bank_adapted u).mono (M.le u) le_rfl).inv
    (M.terminal_discount_integrable u) (.of_forall (fun ω => inv_pos.mpr (M.bank_pos u ω)))
    M.bank (M.bond u) X (fun t ω => ne_of_gt (M.bank_pos t ω))
    (fun t => ((M.bond_adapted u t).div (M.bank_adapted t)).stronglyMeasurable)
    (M.discounted_conditional u)
    (fun t => ((hXm t).div (M.bank_adapted t)).stronglyMeasurable) hXi hX

#print axioms pricing
#print axioms forward_numeraire
end BondMarket
end Asakura.EndToEnd

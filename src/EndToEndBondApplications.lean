import EndToEndBondMarket
import EndToEndTrivialInformation

open MeasureTheory Set
open scoped NNReal
namespace Asakura.EndToEnd.BondMarket
open Asakura.Chapter13
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]

theorem initial_price (M : BondMarket Q)
    (hzero : ∀ A, MeasurableSet[M.F 0] A → Q A = 0 ∨ Q A = 1)
    (hbank : ∀ ω, M.bank 0 ω = 1) (u : ℝ≥0) :
    M.bond u 0 =ᵐ[Q] (fun _ => ∫ ω, (M.bank u ω)⁻¹ ∂Q) := by
  filter_upwards [M.pricing u 0,
    conditional_of_zero_one Q (M.le 0) hzero _ (M.terminal_discount_integrable u)] with ω hp hc
  rw [hp, hbank, one_mul, hc]

/-- No positivity, regularity, or integrability of term rates is supplied
separately: they are defined from the same market's two bonds. -/
theorem forward_term_rate (M : BondMarket Q) (u v : ℝ≥0) (δ : ℝ) :
    IsProbabilityMeasure (M.forwardMeasure v) ∧
    (∀ t, Integrable (fun ω => (M.bond u t ω / M.bond v t ω - 1) / δ)
      (M.forwardMeasure v)) ∧
    (∀ s t, s ≤ t →
      (M.forwardMeasure v)[(fun ω => (M.bond u t ω / M.bond v t ω - 1) / δ)|M.F s]
        =ᵐ[M.forwardMeasure v] (fun ω => (M.bond u s ω / M.bond v s ω - 1) / δ)) := by
  obtain ⟨hp,hi,hm⟩ := M.forward_numeraire v (M.bond u) (M.bond_adapted u)
    (M.discounted_integrable u) (M.discounted_martingale u)
  letI := hp
  exact ⟨hp, term_rate_forward_martingale (M.forwardMeasure v) M.F M.le _ δ hi hm⟩

theorem option_forward_pricing (M : BondMarket Q) (u t : ℝ≥0)
    (payoff : Ω → ℝ)
    (hi : Integrable (fun ω => (M.bank u ω)⁻¹ * payoff ω) Q) :
    IsProbabilityMeasure (M.forwardMeasure u) ∧ Integrable payoff (M.forwardMeasure u) ∧
      (fun ω => M.bank t ω * Q[(fun ω => (M.bank u ω)⁻¹ * payoff ω)|M.F t] ω)
        =ᵐ[Q] (fun ω => M.bond u t ω * (M.forwardMeasure u)[payoff|M.F t] ω) := by
  obtain ⟨hp,hpi,he⟩ := numeraire_payoff_pricing Q (M.le t)
    (fun ω => (M.bank u ω)⁻¹) ((M.bank_adapted u).mono (M.le u) le_rfl).inv
    (M.terminal_discount_integrable u) (.of_forall (fun ω => inv_pos.mpr (M.bank_pos u ω))) payoff hi
  refine ⟨hp,hpi,?_⟩
  filter_upwards [he,M.pricing u t] with ω hω hpω
  rw [hω,hpω]
  exact (mul_assoc _ _ _).symm

#print axioms initial_price
#print axioms forward_term_rate
#print axioms option_forward_pricing
end Asakura.EndToEnd.BondMarket

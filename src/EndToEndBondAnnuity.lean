import EndToEndBondApplications

open MeasureTheory Set
open scoped NNReal
namespace Asakura.EndToEnd.BondMarket
open Asakura.Chapter13
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]

theorem positive_bond_ae (M : BondMarket Q) (u t : ℝ≥0) :
    ∀ᵐ ω ∂Q, 0 < M.bond u t ω := by
  have h := Asakura.FullAudit.exercise_ce_strictly_positive Q (M.le t)
    (M.terminal_discount_integrable u)
    (Filter.Eventually.of_forall (fun ω => inv_pos.mpr (M.bank_pos u ω)))
  filter_upwards [M.pricing u t,h] with ω hp hz
  rw [hp]
  exact mul_pos (M.bank_pos t ω) hz

def annuity (M : BondMarket Q) {J : Type*} [Fintype J]
    (a : J → ℝ) (u : J → ℝ≥0) (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∑ j, a j * M.bond (u j) t ω

theorem annuity_discounted (M : BondMarket Q) {J : Type*} [Fintype J]
    (a : J → ℝ) (u : J → ℝ≥0) :
    (∀ t, Measurable[M.F t] (M.annuity a u t)) ∧
    (∀ t, Integrable (fun ω => M.annuity a u t ω / M.bank t ω) Q) ∧
    (∀ s t, s ≤ t → Q[(fun ω => M.annuity a u t ω / M.bank t ω)|M.F s]
      =ᵐ[Q] (fun ω => M.annuity a u s ω / M.bank s ω)) := by
  have he t : (fun ω => M.annuity a u t ω / M.bank t ω) =
      (fun ω => ∑ j, a j * (M.bond (u j) t ω / M.bank t ω)) := by
    funext ω
    simp [annuity, Finset.sum_div, mul_div_assoc]
  refine ⟨fun t => Finset.measurable_sum _ (fun j _ => (M.bond_adapted (u j) t).const_mul (a j)),?_,?_⟩
  · intro t
    rw [he]
    exact integrable_finset_sum _ (fun j _ => (M.discounted_integrable (u j) t).const_mul (a j))
  · intro s t hst
    rw [he,he]
    exact finite_annuity_conditional Q a _ _ (fun j => M.discounted_integrable (u j) t)
      (fun j => M.discounted_martingale (u j) s t hst)

theorem annuity_positive_ae (M : BondMarket Q) {J : Type*} [Fintype J] [Nonempty J]
    (a : J → ℝ) (ha : ∀ j, 0 < a j) (u : J → ℝ≥0) (t : ℝ≥0) :
    ∀ᵐ ω ∂Q, 0 < M.annuity a u t ω := by
  filter_upwards [ae_all_iff.mpr (fun j => M.positive_bond_ae (u j) t)] with ω hω
  apply Finset.sum_pos
  · intro j _
    exact mul_pos (ha j) (hω j)
  · exact Finset.univ_nonempty

#print axioms positive_bond_ae
#print axioms annuity_discounted
#print axioms annuity_positive_ae
end Asakura.EndToEnd.BondMarket

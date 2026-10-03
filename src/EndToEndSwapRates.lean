import EndToEndSwapMeasure

open MeasureTheory Set
open scoped NNReal
namespace Asakura.EndToEnd.BondMarket
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]

theorem swap_rate_martingale (M : BondMarket Q) {J : Type*} [Fintype J] [Nonempty J]
    (a : J → ℝ) (ha : ∀ j, 0 < a j) (u : J → ℝ≥0) (S first last : ℝ≥0) :
    IsProbabilityMeasure (M.swapMeasure a u S) ∧
    (∀ t : Iic S, Integrable
      (fun ω => (M.bond first t ω - M.bond last t ω) / M.annuity a u t ω)
      (M.swapMeasure a u S)) ∧
    (∀ s t : Iic S, s ≤ t → (M.swapMeasure a u S)[
      (fun ω => (M.bond first t ω - M.bond last t ω) / M.annuity a u t ω)|M.F s]
        =ᵐ[M.swapMeasure a u S]
      (fun ω => (M.bond first s ω - M.bond last s ω) / M.annuity a u s ω)) := by
  let X := fun t ω => M.bond first t ω - M.bond last t ω
  have hi t : Integrable (fun ω => X t ω / M.bank t ω) Q := by
    simpa [X,sub_div,Pi.sub_def] using (M.discounted_integrable first t).sub (M.discounted_integrable last t)
  have hm s t (hst : s ≤ t) : Q[(fun ω => X t ω / M.bank t ω)|M.F s]
      =ᵐ[Q] (fun ω => X s ω / M.bank s ω) := by
    have hsub := condExp_sub (M.discounted_integrable first t)
      (M.discounted_integrable last t) (M.F s)
    have h1 := M.discounted_martingale first s t hst
    have h2 := M.discounted_martingale last s t hst
    simpa only [X,sub_div,Pi.sub_def] using hsub.trans (h1.sub h2)
  exact M.swap_numeraire a ha u S X
    (fun t => (M.bond_adapted first t).sub (M.bond_adapted last t)) hi hm

#print axioms swap_rate_martingale
end Asakura.EndToEnd.BondMarket

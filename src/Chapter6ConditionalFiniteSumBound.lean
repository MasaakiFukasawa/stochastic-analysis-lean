import Chapter6ConditionalInnerBound

open MeasureTheory Set Filter Finset
open scoped Topology BigOperators
namespace Asakura.Chapter6

theorem conditional_finite_sum_abs_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (n : ℕ) (X a : ℕ → Ω → ℝ)
    (hi : ∀ k∈range n,Integrable (X k) P) (G : MeasurableSpace Ω)
    (hb : ∀ k∈range n,∀ᵐ w ∂P,|P[X k|G] w|≤a k w) :
    ∀ᵐ w ∂P,|P[(fun w => ∑ k∈range n,X k w)|G] w|≤∑ k∈range n,a k w := by
  have hc := condExp_finsetSum hi G
  filter_upwards [hc,ae_all_iff.2 (fun k => ae_all_iff.2 (hb k))] with w hc hb
  simp only [Finset.sum_fn,Finset.sum_apply] at hc
  rw [hc]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (sum_le_sum (fun k hk => hb k hk))

end Asakura.Chapter6

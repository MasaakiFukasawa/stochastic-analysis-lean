import Kolmogorov

open MeasureTheory Set
namespace Asakura

lemma holder_all_exponents_common_event {T Ω : Type*} [PseudoMetricSpace T]
    [MeasurableSpace Ω] (P : Measure Ω) (Y : T → Ω → ℝ) (H : ℝ)
    (hdiam : ∀ s t : T, dist s t ≤ 1)
    (h : ∀ α : ℝ, 0 < α → α < H →
      ∀ᵐ ω ∂P, ∃ C : ℝ, 0 ≤ C ∧ ∀ s t,
        dist (Y s ω) (Y t ω) ≤ C * (dist s t)^α) :
    ∀ᵐ ω ∂P, ∀ α : ℝ, 0 ≤ α → α < H →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ s t,
        dist (Y s ω) (Y t ω) ≤ C * (dist s t)^α := by
  have hq : ∀ᵐ ω ∂P, ∀ q : ℚ, (0 : ℝ) < q → (q : ℝ) < H →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ s t,
        dist (Y s ω) (Y t ω) ≤ C * (dist s t)^(q : ℝ) := by
    apply ae_all_iff.mpr
    intro q
    by_cases hq0 : (0 : ℝ) < q
    · by_cases hqH : (q : ℝ) < H
      · filter_upwards [h q hq0 hqH] with ω hω using fun _ _ => hω
      · exact Filter.Eventually.of_forall (by intro ω _ h'; exact (hqH h').elim)
    · exact Filter.Eventually.of_forall (by intro ω h'; exact (hq0 h').elim)
  filter_upwards [hq] with ω hω
  intro α hα hαH
  obtain ⟨q,hαq,hqH⟩ := exists_rat_btwn hαH
  obtain ⟨C,hC,hbound⟩ := hω q (hα.trans_lt hαq) hqH
  refine ⟨C,hC,fun s t => (hbound s t).trans ?_⟩
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_ge' dist_nonneg (hdiam s t) hα hαq.le) hC
end Asakura

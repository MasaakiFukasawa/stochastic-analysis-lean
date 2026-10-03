import EndToEndHJMOriginalDrift

open MeasureTheory Set Filter
namespace Asakura.EndToEnd

/-- Countably many finite time/maturity boxes imply one product-a.e. drift
identity on the whole positive quadrant. No uncountable intersection is used. -/
theorem positive_quadrant_ae_of_boxes {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (D : Ω → ℝ → ℝ → Prop)
    (h : ∀ n : ℕ,∀ᵐ w ∂P,∀ᵐ r ∂volume,r∈Ioo (0:ℝ) (n+1) →
      ∀ᵐ u ∂volume,u∈Ioo (0:ℝ) (n+1) → D w r u) :
    ∀ᵐ w ∂P,∀ᵐ r ∂volume,0<r → ∀ᵐ u ∂volume,0<u → D w r u := by
  filter_upwards [ae_all_iff.mpr h] with w hw
  filter_upwards [ae_all_iff.mpr hw] with r hr hpos
  have hu (n : ℕ) : ∀ᵐ u ∂volume,r<(n:ℝ)+1 → u∈Ioo (0:ℝ) (n+1) → D w r u := by
    by_cases hn : r<(n:ℝ)+1
    · filter_upwards [hr n ⟨hpos,hn⟩] with u hu hnr hui
      exact hu hui
    · exact Filter.Eventually.of_forall fun _ hnr => (hn hnr).elim
  filter_upwards [ae_all_iff.mpr hu] with u hu hupos
  obtain ⟨n,hn⟩ := exists_nat_gt (max r u)
  exact hu n (by linarith [le_max_left r u]) ⟨hupos,by linarith [le_max_right r u]⟩

#print axioms positive_quadrant_ae_of_boxes
end Asakura.EndToEnd

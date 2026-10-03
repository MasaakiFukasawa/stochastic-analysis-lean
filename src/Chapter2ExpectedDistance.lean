import Chapter2IntegrandMetricEquivalence
import Chapter2LocalLpQuotient

open MeasureTheory Set Filter
open scoped Topology ENNReal Classical
namespace Asakura.Chapter2Complete
set_option backward.isDefEq.respectTransparency false

/-- Taking expectations of the bounded pathwise distance gives precisely
the pseudometric and distance-zero identification used for H_A^p. -/
theorem expected_distance_laws
    {Ω E : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (d : Ω → E → E → ℝ)
    (hm : ∀ x y, Measurable (fun ω => d ω x y))
    (hb : ∀ ω x y, 0 ≤ d ω x y ∧ d ω x y ≤ 1)
    (hs : ∀ ω x, d ω x x = 0)
    (hc : ∀ ω x y, d ω x y = d ω y x)
    (ht : ∀ ω x y z, d ω x z ≤ d ω x y+d ω y z) :
    (∀ x, (∫ ω, d ω x x ∂P) = 0) ∧
    (∀ x y, (∫ ω, d ω x y ∂P) = ∫ ω, d ω y x ∂P) ∧
    (∀ x y z, (∫ ω, d ω x z ∂P) ≤ (∫ ω, d ω x y ∂P)+(∫ ω, d ω y z ∂P)) ∧
    (∀ x y, (∫ ω, d ω x y ∂P) = 0 ↔ ∀ᵐ ω ∂P, d ω x y = 0) := by
  have hi x y : Integrable (fun ω => d ω x y) P :=
    Integrable.of_bound (hm x y).aestronglyMeasurable 1
      (.of_forall fun ω => by rw [Real.norm_eq_abs,abs_of_nonneg (hb ω x y).1]; exact (hb ω x y).2)
  refine ⟨?_,?_,?_,?_⟩
  · intro x
    simp only [hs,integral_zero]
  · intro x y
    exact integral_congr_ae (.of_forall fun ω => hc ω x y)
  · intro x y z
    rw [← integral_add (hi x y) (hi y z)]
    exact integral_mono (hi x z) ((hi x y).add (hi y z)) (fun ω => ht ω x y z)
  · intro x y
    exact integral_eq_zero_iff_of_nonneg_ae (.of_forall fun ω => (hb ω x y).1) (hi x y)

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.expected_distance_laws

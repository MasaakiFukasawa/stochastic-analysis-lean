import Chapter9ReverseLocalTest

open MeasureTheory Set
open scoped ContDiff
namespace Asakura.Chapter9
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

theorem ou_reverse_drift_coordinate_continuous {d : ℕ}
    (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ] (i : Fin d) :
    ContinuousOn (fun z => ouReverseDrift μ z i) (Ioi 0 ×ˢ univ) := by
  apply (ou_reverse_generator_continuous μ (fun x => x i) (by fun_prop)).congr
  intro z _
  exact (reverse_generator_coordinate μ z.1 i z.2).symm

/-- Coordinates of the actual compensated reverse process are local
 martingales, derived from the smooth compact tests by state-ball stopping. -/
theorem reverse_coordinate_local_martingale {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ}
    (μ : Measure (Fin d → ℝ)) (T b : ℝ) (hb : 0≤b)
    (F : HalfClosedTime → MeasurableSpace Ω) (Z : ℝ → Ω → Fin d → ℝ)
    (hlocal : ∀ q,ContDiff ℝ ∞ q → LocalMProcessWitness P F
      (fun t w => reverseCompensated μ T Z q (finitePrefixTime b hb t).val w))
    (i : Fin d) :
    LocalMProcessWitness P F (fun t w =>
      Z (finitePrefixTime b hb t).val w i-Z 0 w i-
        ∫ r in 0..(finitePrefixTime b hb t).val,ouReverseDrift μ (T-r,Z r w) i) := by
  simpa only [reverseCompensated,reverse_generator_coordinate] using hlocal (fun x => x i) (by fun_prop)

/-- Coordinate products give the second martingale identity needed for
 identifying every diagonal and cross bracket. -/
theorem reverse_product_local_martingale {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ}
    (μ : Measure (Fin d → ℝ)) (T b : ℝ) (hb : 0≤b)
    (F : HalfClosedTime → MeasurableSpace Ω) (Z : ℝ → Ω → Fin d → ℝ)
    (hlocal : ∀ q,ContDiff ℝ ∞ q → LocalMProcessWitness P F
      (fun t w => reverseCompensated μ T Z q (finitePrefixTime b hb t).val w))
    (i j : Fin d) :
    LocalMProcessWitness P F (fun t w =>
      Z (finitePrefixTime b hb t).val w i*Z (finitePrefixTime b hb t).val w j-Z 0 w i*Z 0 w j-
        ∫ r in 0..(finitePrefixTime b hb t).val,
          Z r w j*ouReverseDrift μ (T-r,Z r w) i+
          Z r w i*ouReverseDrift μ (T-r,Z r w) j+2*(if i=j then 1 else 0)) := by
  classical
  simpa only [reverseCompensated,reverse_generator_coordinate_product] using
    hlocal (fun x => x i*x j) (by fun_prop)
end Asakura.Chapter9

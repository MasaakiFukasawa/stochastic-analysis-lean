import Chapter2DisjointMeasurePasting

open MeasureTheory Set
open scoped ENNReal
namespace Asakura.Chapter2Complete
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

variable {S : Type*} [MeasurableSpace S]
noncomputable def compatibleMeasurePaste (μ : ℕ → Measure S) (B : ℕ → Set S) : Measure S :=
  Measure.sum (fun n => (μ n).restrict (disjointed B n))

theorem compatible_measure_paste_sigmaFinite (μ : ℕ → Measure S) [∀ n, SigmaFinite (μ n)]
    (B : ℕ → Set S) (hB : ∀ n, MeasurableSet (B n)) :
    SigmaFinite (compatibleMeasurePaste μ B) :=
  disjoint_sum_sigmaFinite μ (disjointed B) (MeasurableSet.disjointed hB) (disjoint_disjointed B)

/-- Compatible finite-horizon measures determine one measure on the whole
open time interval; its restrictions are exactly the original measures. -/
theorem compatible_measure_paste_restrict (μ : ℕ → Measure S) (B : ℕ → Set S)
    (hB : ∀ n, MeasurableSet (B n))
    (hself : ∀ n, (μ n).restrict (B n) = μ n)
    (hcompat : ∀ j n, (μ j).restrict (B n) = (μ n).restrict (B j)) (n : ℕ) :
    (compatibleMeasurePaste μ B).restrict (B n) = μ n := by
  have he j : ((μ j).restrict (disjointed B j)).restrict (B n) =
      (μ n).restrict (disjointed B j) := by
    rw [Measure.restrict_comm (hB n),hcompat j n]
    exact Measure.restrict_restrict_of_subset (disjointed_subset B j)
  rw [compatibleMeasurePaste,Measure.restrict_sum _ (hB n)]
  simp_rw [he]
  rw [← Measure.restrict_iUnion (disjoint_disjointed B) (MeasurableSet.disjointed hB),iUnion_disjointed]
  calc
    (μ n).restrict (⋃ j, B j) = ((μ n).restrict (B n)).restrict (⋃ j, B j) := by rw [hself n]
    _ = ((μ n).restrict (⋃ j, B j)).restrict (B n) := Measure.restrict_comm (MeasurableSet.iUnion hB)
    _ = (μ n).restrict (B n) := Measure.restrict_restrict_of_subset (subset_iUnion B n)
    _ = μ n := hself n

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.compatible_measure_paste_restrict
#print axioms Asakura.Chapter2Complete.compatible_measure_paste_sigmaFinite

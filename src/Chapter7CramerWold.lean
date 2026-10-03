import Mathlib.MeasureTheory.Measure.LevyConvergence

open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace Asakura.Chapter7

lemma cramer_wold_euclidean {Ω Γ ι : Type*} [MeasurableSpace Ω] [MeasurableSpace Γ] [Fintype ι]
    (P : Measure Ω) (Q : Measure Γ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (X : ℕ → Ω → EuclideanSpace ℝ ι) (Y : Γ → EuclideanSpace ℝ ι)
    (hX : ∀ n,AEMeasurable (X n) P) (hY : AEMeasurable Y Q)
    (h : ∀ v,TendstoInDistribution (fun n w => inner ℝ (X n w) v) atTop
      (fun z => inner ℝ (Y z) v) (fun _ => P) Q) :
    TendstoInDistribution X atTop Y (fun _ => P) Q := by
  apply TendstoInDistribution.of_tendsto_charFun hX hY
  intro v
  simpa only [charFun_map_eq_charFun_map_inner_one (hX _) v,
    charFun_map_eq_charFun_map_inner_one hY v] using (h v).tendsto_charFun 1

end Asakura.Chapter7

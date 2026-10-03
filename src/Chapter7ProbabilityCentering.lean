import Chapter7ProbabilityErrorAssembly

open MeasureTheory Filter
open scoped Topology
namespace Asakura.Chapter7

lemma probability_centering {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ) (c : ℝ) :
    TendstoInMeasure P X atTop (fun _ => c) ↔
      TendstoInMeasure P (fun n w => X n w-c) atTop (fun _ => 0) := by
  rw [tendstoInMeasure_iff_dist,tendstoInMeasure_iff_dist]
  simp only [Real.dist_eq,sub_zero]

end Asakura.Chapter7

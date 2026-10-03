import Chapter7EmpiricalQuadraticAlgebra
import Chapter7BrownianEstimatorConsistency
import Chapter7BrownianQuadraticStatistic

open MeasureTheory Set Filter Matrix Finset
open scoped Topology BigOperators
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

lemma brownian_matrix_contraction {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (H S : Matrix (Fin d) (Fin d) ℝ) (T : ℝ) (hT : 0<T) (n : ℕ) (hn : 0<n) (w : Ω) :
    Real.sqrt (n:ℝ)*(∑ i,∑ j,H i j*(realizedCovarianceEntry B (S i) (S j) T n w-(S*S.transpose) i j))=
      brownianQuadraticStatistic B (S.transpose*H*S) T n w := by
  let D := fun (k : Fin n) j => B.W j (realTimeClamp (((k:ℝ)+1)*(T/n))) w-B.W j (realTimeClamp ((k:ℝ)*(T/n))) w
  have hentry i j : realizedCovarianceEntry B (S i) (S j) T n w=
      (1/T)*∑ k,(S.mulVec (D k)) i*(S.mulVec (D k)) j := by
    dsimp only [realizedCovarianceEntry,Matrix.mulVec,dotProduct,D]
    ring
  simp only [hentry,empirical_quadratic_algebra H S D T hT.ne' hn]
  change Real.sqrt (n:ℝ)*((1/T)*∑ k : Fin n,((∑ i,∑ j,(S.transpose*H*S) i j*D k i*D k j)-(T/n)*(∑ i,(S.transpose*H*S) i i)))=
    (Real.sqrt (n:ℝ)/T)*∑ k : Fin n,((∑ i,∑ j,(S.transpose*H*S) i j*D k i*D k j)-(T/n)*(∑ i,(S.transpose*H*S) i i))
  ring

end Asakura.Chapter7

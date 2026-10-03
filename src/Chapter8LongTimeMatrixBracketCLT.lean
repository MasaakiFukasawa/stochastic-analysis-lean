import Chapter8LongTimeVectorCLT
import Chapter8ProbabilityLinear

open MeasureTheory ProbabilityTheory Set Filter Matrix
open scoped Topology NNReal ENNReal BigOperators RealInnerProductSpace
namespace Asakura.Chapter8
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
  Asakura.Chapter4 Asakura.Chapter7
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

/-- The vector long-time CLT with exactly the entrywise matrix bracket
convergence supplied by the information-matrix ergodic argument. -/
theorem long_time_matrix_bracket_clt {Ω : Type*} [m : MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : HalfClosedTime → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t ≤ m)
    (M : Fin d → HalfClosedTime → Ω → ℝ)
    (C : Fin d → Fin d → HalfClosedTime → Ω → ℝ)
    (hM : ∀ i, LocalMProcessWitness P F (M i))
    (hC : ∀ i j, LocalCovarianceWitness P F (M i) (M j) (C i j))
    (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosDef)
    (havg : ∀ i j,TendstoInMeasure P (fun T ω => C i j (realTimeClamp T) ω/T)
      atTop (fun _ => S i j))
    (T : ℕ → ℝ) (hT : ∀ n,0 < T n) (hTlim : Tendsto T atTop atTop) :
    TendstoInDistribution
      (fun n ω => WithLp.toLp 2 (fun i => M i (realTimeClamp (T n)) ω/Real.sqrt (T n))) atTop
      id (fun _ => P) (multivariateGaussian 0 S) := by
  apply long_time_vector_clt P F hF hle M C hM hC S hS _ T hT hTlim
  intro v
  have hh := probability_quadratic_projection P atTop
    (fun T ω i j => C i j (realTimeClamp T) ω/T) S havg v
  convert hh using 1
  · funext t ω
    simp only [Finset.mul_sum,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    ring
  · funext ω
    simp only [dotProduct,Matrix.mulVec,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring

end Asakura.Chapter8

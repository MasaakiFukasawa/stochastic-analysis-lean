import Chapter7OriginalEstimatorDrift
import Chapter7FiniteProbabilitySum

open MeasureTheory Matrix Set Filter Finset
open scoped Topology BigOperators
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

theorem matrix_drift_negligible {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (H S : Matrix (Fin d) (Fin d) ℝ) (T K : ℝ) (hT : 0<T) (hK : 0≤K)
    (b : Fin d → ℝ → Ω → ℝ) (x : Fin d → Ω → ℝ)
    (hbc : ∀ i w,Continuous (fun r => b i r w))
    (hba : ∀ i r,r∈Icc 0 T → Measurable[B.F (realTimeClamp r)] (b i r))
    (hbb : ∀ i r,r∈Icc 0 T → ∀ w,|b i r w|≤K) :
    TendstoInMeasure P (fun n w => Real.sqrt ((n+1:ℕ):ℝ)*
      (∑ i,∑ j,H i j*(realizedProcessEntry (driftedProjectionProcess B (S i) (b i) (x i))
        (driftedProjectionProcess B (S j) (b j) (x j)) T (n+1) w-
        realizedCovarianceEntry B (S i) (S j) T (n+1) w))) atTop (fun _ => 0) := by
  let E := fun i j n w => Real.sqrt ((n+1:ℕ):ℝ)*
      (realizedProcessEntry (driftedProjectionProcess B (S i) (b i) (x i))
        (driftedProjectionProcess B (S j) (b j) (x j)) T (n+1) w-
        realizedCovarianceEntry B (S i) (S j) T (n+1) w)
  have he i j : TendstoInMeasure P (fun n w => H i j*E i j n w) atTop (fun _ => 0) := by
    have hp := original_estimator_drift_negligible P B (S i) (S j) T K hT hK
      (b i) (b j) (x i) (x j) (hbc i) (hbc j) (hba i) (hba j) (hbb i) (hbb j)
    simpa only [mul_zero] using probability_const_mul P (E i j) (fun _ => 0) hp (H i j)
  have hj i := probability_finite_sum_zero P univ (fun j n w => H i j*E i j n w) (fun j _ => he i j)
  have hi := probability_finite_sum_zero P univ (fun i n w => ∑ j,H i j*E i j n w) (fun i _ => hj i)
  apply hi.congr_left
  intro n
  apply ae_of_all
  intro w
  simp only [E,mul_sum]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  ring

end Asakura.Chapter7

import Chapter2CumulativeTests
import Chapter2StepClipping
import Chapter2StepEnergyAlgebra

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
set_option maxHeartbeats 1000000

/-- A holding-interval integral is an increment of the cumulative measure,
including the endpoint convention [a,b) versus (a,b]. -/
theorem elementary_cumulative_measure_integral
    (μ : Measure ℝ) [IsFiniteMeasure μ] [NullSingletonClass μ]
    (a b t z : ℝ) (hab : a ≤ b) :
    (∫ r in Iic t, (Ico a b).indicator (fun _ => z) r ∂μ) =
      z*(μ.real (Iic (min b t))-μ.real (Iic (min a t))) := by
  let g := (Iic t).indicator (fun _ : ℝ => (1:ℝ))
  have hg : Integrable g μ := (integrable_const (1:ℝ)).indicator measurableSet_Iic
  have hi (s : ℝ) : (∫ r in Iic s, g r ∂μ) = μ.real (Iic (min s t)) := by
    simp only [g,integral_indicator measurableSet_Iic,integral_const,smul_eq_mul,mul_one,
      Measure.real,Measure.restrict_restrict measurableSet_Iic,Measure.restrict_apply MeasurableSet.univ,
      Set.univ_inter,Iic_inter_Iic,min_comm t s]
  have he : (fun r => ((Ico a b).indicator (fun _ => z) r)*g r) =
      (Iic t).indicator ((Ico a b).indicator (fun _ => z)) := by
    funext r
    by_cases hr : r ∈ Iic t <;> simp [g,hr]
  have h := cumulative_increment_elementary_test μ g hg a b z hab
  rw [hi b,hi a,he,integral_indicator measurableSet_Iic] at h
  exact h.symm

/-- The square of the actual step integrand integrates to the energy sum
obtained by applying the local-covariation formula twice. -/
theorem grid_stieltjes_square_integral
    (μ : Measure ℝ) [IsFiniteMeasure μ] [NullSingletonClass μ]
    (N : ℕ) (u : ℕ → ℝ) (hu : StrictMonoOn u (Iic N)) (G : ℕ → ℝ) (t : ℝ) :
    (∫ r in Iic t,
      (∑ j ∈ Finset.range N, (Ico (u j) (u (j+1))).indicator (fun _ => G j) r)^2 ∂μ) =
      ∑ j ∈ Finset.range N, G j ^ 2 * stepIncrement (u j) (u (j+1)) (fun r => μ.real (Iic r)) t := by
  classical
  have he : (fun r => (∑ j ∈ Finset.range N, (Ico (u j) (u (j+1))).indicator (fun _ => G j) r)^2) =
      (fun r => ∑ j ∈ Finset.range N, (Ico (u j) (u (j+1))).indicator (fun _ => G j ^ 2) r) := by
    funext r
    exact grid_step_map N u hu G (fun x => x^2) (by norm_num) r
  rw [he,integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro j hj
    have hjn : j < N := Finset.mem_range.1 hj
    exact elementary_cumulative_measure_integral μ (u j) (u (j+1)) t (G j^2)
      (hu.monotoneOn hjn.le (show j+1 ∈ Iic N by change j+1 ≤ N; omega) (by omega))
  · intro j hj
    exact ((integrable_const (G j^2)).indicator measurableSet_Ico).integrableOn

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.elementary_cumulative_measure_integral
#print axioms Asakura.Chapter2Complete.grid_stieltjes_square_integral

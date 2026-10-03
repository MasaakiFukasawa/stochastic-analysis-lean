import Chapter7GridMartingaleConstruction
import Chapter7BrownianCellEnergy
import Chapter7MatrixClockProbability

open MeasureTheory Set Filter Finset
open scoped Topology BigOperators
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false

lemma normalized_grid_energy {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (K : Fin d → Fin d → ℝ) (T t : ℝ) (n : ℕ) (hT : 0<T) (ht0 : 0≤t) (htT : t≤T) (hn : 0<n) (w : Ω) :
    (∫ r in 0..t,∑ i,((2*Real.sqrt (n:ℝ)/T)*brownianGridIntegrand B (K i) (T/n) (n+1) (w,r))^2)=
      ∑ i,brownianCellClock B (K i) T t n w := by
  have hh : 0≤T/(n:ℝ) := div_nonneg hT.le (Nat.cast_nonneg _)
  have ha : (2*Real.sqrt (n:ℝ)/T)^2=4*(n:ℝ)/T^2 := by
    rw [div_pow,mul_pow,Real.sq_sqrt (Nat.cast_nonneg _)]
    norm_num
  have hi i : IntervalIntegrable (fun r => ((2*Real.sqrt (n:ℝ)/T)*brownianGridIntegrand B (K i) (T/n) (n+1) (w,r))^2) volume 0 t := by
    simpa only [mul_pow] using ((brownian_grid_integrand_regular P B (K i) (T/n) hh (n+1)).2.2 t ht0 w).const_mul ((2*Real.sqrt (n:ℝ)/T)^2)
  rw [intervalIntegral.integral_finsetSum (fun i _ => hi i)]
  apply sum_congr rfl
  intro i _
  simp only [mul_pow,ha,intervalIntegral.integral_const_mul]
  exact brownian_grid_energy_clock P B (K i) T t n hT ht0 htT hn w

end Asakura.Chapter7

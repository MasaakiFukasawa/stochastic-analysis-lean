import Chapter7NormalizedGridClock
import Chapter7ScaledFiniteCLT

open MeasureTheory ProbabilityTheory Set Filter Finset
open scoped Topology BigOperators NNReal
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

/-- Construction and bracket convergence for the martingale in the written
proof, from the Brownian driver and the deterministic coefficient matrix. -/
theorem grid_martingale_clock_limit {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (K : Fin d → Fin d → ℝ) (T : ℝ) (hT : 0<T) :
    ∃ (N : ℕ → Fin d → HalfClosedTime → Ω → ℝ) (C : ℕ → HalfClosedTime → Ω → ℝ),
      (∀ n i,LocalMProcessWitness P B.F (N n i)) ∧
      (∀ n i,ItoCovarianceFormula P B.F (B.W i)
        (fun z => (2*Real.sqrt ((n+1:ℕ):ℝ)/T)*brownianGridIntegrand B (K i) (T/(n+1)) (n+2) z) (N n i)) ∧
      (∀ n,LocalMProcessWitness P B.F (fun t w => ∑ i,N n i t w)) ∧
      (∀ n,LocalCovarianceWitness P B.F (fun t w => ∑ i,N n i t w) (fun t w => ∑ i,N n i t w) (C n)) ∧
      (∀ t,0≤t → t≤T → TendstoInMeasure P (fun n => C n (realTimeClamp t)) atTop
        (fun _ => (2*(∑ i,∑ j,(K i j)^2)/T)*t)) := by
  have hex n := brownian_grid_martingale_constructed P B K (T/((n+1:ℕ):ℝ))
    (2*Real.sqrt ((n+1:ℕ):ℝ)/T) (div_nonneg hT.le (Nat.cast_nonneg _)) (n+2)
  choose N C hN hNI hM hC hCe using hex
  refine ⟨N,C,hN,?_,hM,hC,?_⟩
  · intro n i
    simpa only [Nat.cast_add,Nat.cast_one] using hNI n i
  · intro t ht0 htT
    have he n : C n (realTimeClamp t) =ᵐ[P] fun w => ∑ i,brownianCellClock B (K i) T t (n+1) w := by
      filter_upwards [hCe n t ht0] with w hw
      rw [hw]
      exact normalized_grid_energy P B K T t (n+1) hT ht0 htT (Nat.succ_pos _) w
    exact (matrix_cell_clock_probability P B K T t hT ht0 htT).congr_left (fun n => (he n).symm)

end Asakura.Chapter7

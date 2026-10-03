import Chapter5WeightedSquareCalculus

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 3600000
set_option backward.isDefEq.respectTransparency false

/-- The weighted stochastic energy identity obtained from the actual
constructed Ito formula. No energy identity is an input assumption. -/
theorem weighted_energy_ito
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X A M C : ClosedTime T → Ω → ℝ)
    (hX : SemimartingaleDecomposition P F X A M)
    (hC : LocalCovarianceWitness P F M M C)
    (R : ℝ) (hR : 0 ≤ R) (hRT : (R:EReal) < T)
    (β : ℝ)
    (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n) (hcm : Monotone c)
    (hcT : ∀ n, (c n:EReal) < T)
    (hcc : ∀ t, t < ⊤ → ∃ n, t < realTimeClamp (T := T) (c n))
    (B : Ω × ℝ → ℝ) (hBm : ∀ w, Measurable (fun r => B (w,r)))
    (hBi : ∀ n, ∀ᵐ w ∂P, IntervalIntegrable (fun r => B (w,r)) volume 0 (c n))
    (hAB : ∀ n, ∀ᵐ w ∂P, ∀ r ∈ Icc 0 (c n), A (realTimeClamp r) w = A ⊥ w + ∫ s in 0..r, B (w,s))
    (G : Ω × ℝ → ℝ) (hGm : ∀ w, Measurable (fun r => G (w,r)))
    (hGi : ∀ n, ∀ᵐ w ∂P, IntervalIntegrable (fun r => G (w,r)) volume 0 (c n))
    (hCG : ∀ n, ∀ᵐ w ∂P, ∀ r ∈ Icc 0 (c n), C (realTimeClamp r) w = ∫ s in 0..r, G (w,s)) :
    ∃ N : ClosedTime T → Ω → ℝ,
      LocalMProcessWitness P F N ∧
      ItoCovarianceFormula P F M
        (fun z => 2*Real.exp (β*(finitePrefixTime (T := T) R hR (realTimeClamp z.2)).val)*
          X (realTimeClamp z.2) z.1) N ∧
      ∀ d : ℝ, 0 ≤ d → d ≤ R →
        (fun w => Real.exp (β*d)*(X (realTimeClamp d) w)^2) =ᵐ[P]
          fun w => (X ⊥ w)^2 + N (realTimeClamp d) w +
            (∫ r in 0..d, β*Real.exp (β*r)*(X (realTimeClamp r) w)^2) +
            (∫ r in 0..d, 2*Real.exp (β*r)*X (realTimeClamp r) w*B (w,r)) +
            (∫ r in 0..d, Real.exp (β*r)*G (w,r)) := by
  obtain ⟨N,hN,hNI,he⟩ := time_space_drift_ito P hT F hF hle hnull
    X A M C hX hC R hR hRT (weightedSquare β) ((weightedSquare_smooth β).of_le (by norm_num))
    c hc hcm hcT hcc B hBm hBi hAB G hGm hGi hCG
  refine ⟨N,hN,?_,?_⟩
  · simpa only [weightedSquare_space_derivative,Matrix.cons_val_zero,Matrix.cons_val_one] using hNI
  intro d hd hdR
  filter_upwards [he d hd hdR] with w hw
  simp only [weightedSquare_time_derivative,weightedSquare_space_derivative,weightedSquare_space_second,
    weightedSquare,Matrix.cons_val_zero,Matrix.cons_val_one,mul_zero,Real.exp_zero,one_mul] at hw
  have hint : (∫ r in 0..d, 2*Real.exp (β*r)*G (w,r))/2 = ∫ r in 0..d, Real.exp (β*r)*G (w,r) := by
    rw [← intervalIntegral.integral_div]
    apply intervalIntegral.integral_congr
    intro r hr
    dsimp only
    ring
  rw [hint] at hw
  exact hw

end Asakura.Chapter5

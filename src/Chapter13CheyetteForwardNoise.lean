import Chapter6FiniteWeightedIto
import Chapter4BrownianSystem

open MeasureTheory Set
namespace Asakura.Chapter13
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter6
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- The random term of the Cheyette forward curve is exactly the
stochastic integral of Sigma-transpose g, component by component. -/
theorem cheyette_forward_noise {Ω:Type*} {m:MeasurableSpace Ω}
    (P:Measure Ω) [IsProbabilityMeasure P] {n d:ℕ} (B:BrownianSystem P d)
    (S:Fin n → Fin d → Ω × ℝ → ℝ) (N:Fin n → Fin d → HalfClosedTime → Ω → ℝ)
    (hN:∀i j,LocalMProcessWitness P B.F (N i j))
    (hNI:∀i j,ItoCovarianceFormula P B.F (B.W j) (S i j) (N i j)) (g:Fin n → ℝ) :
    (∀j,LocalMProcessWitness P B.F (fun t w => ∑i,g i*N i j t w) ∧
      ItoCovarianceFormula P B.F (B.W j) (fun z => ∑i,g i*S i j z) (fun t w => ∑i,g i*N i j t w)) ∧
      ∀t w,(∑j,∑i,g i*N i j t w)=∑i,g i*(∑j,N i j t w) := by
  constructor
  · intro j
    exact finite_weighted_ito P (by simp : (0:EReal)<⊤) B.F B.mono B.le B.null (B.W j) (B.martingale j)
      (fun i => S i j) (fun i => N i j) (fun i => hN i j) (fun i => hNI i j) g
  · intro t w
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun i _ => (Finset.mul_sum _ _ _).symm)
end Asakura.Chapter13
#print axioms Asakura.Chapter13.cheyette_forward_noise

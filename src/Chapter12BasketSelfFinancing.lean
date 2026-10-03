import Chapter12BasketMartingaleAllocation
import Chapter12BasketStockNormalization
import Chapter12AsianSelfFinancing

open MeasureTheory Set Filter
open scoped ENNReal BigOperators
namespace Asakura.Chapter12
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false

/-- The inverse volatility allocation is realized by actual self-financing
stock/bank strategies; their martingale gains sum to the original Clark gain. -/
theorem basket_allocated_self_financing {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P (d+1))
    (A : Matrix (Fin (d+1)) (Fin (d+1)) ℝ) (hA : A.det≠0)
    (x : Fin (d+1) → ℝ) (hx : ∀ i,0<x i) (r : ℝ)
    (φ : Fin (d+1) → progressiveEnergyIntegrands B.F canonicalClock (P.prod (volume.restrict (Ioi (0:ℝ)))))
    (N : Fin (d+1) → HalfClosedTime → Ω → ℝ)
    (hN : ∀ j,ContinuousM2Witness P B.F (N j))
    (hNI : ∀ j,ItoCovarianceFormula P B.F (B.W j) (φ j).val (N j)) :
    let σ := fun i => Real.sqrt (∑ j,A i j^2)
    let W := fun i => brownianUnitDirection P B (fun j => A i j/σ i)
      (volatility_row_normalization A hA i).2.2.1
    ∃ ψ : Fin (d+1) → progressiveEnergyIntegrands B.F canonicalClock (P.prod (volume.restrict (Ioi (0:ℝ)))),
    ∃ M : Fin (d+1) → HalfClosedTime → Ω → ℝ,
      (∀ i z,(ψ i).val z=∑ j,(A.transpose)⁻¹ i j*(φ j).val z) ∧
      (∀ i,ScalarReplication P (W i) 0 (x i) (σ i) r 0 (σ i • ψ i) (M i)) ∧
      (∀ᵐ w ∂P,∀ t,t<⊤ → (∑ i,M i t w)=(∑ j,N j t w)) ∧
      ∀ i t w,geometricFlow (x i) r (σ i) ![t,(W i).W 0 (realTimeClamp t) w]=
        x i*Real.exp ((r-(∑ j,A i j^2)/2)*t+∑ j,A i j*B.W j (realTimeClamp t) w) := by
  intro σ W
  obtain ⟨ψ,M,hψ,hM,hMI,he⟩ := basket_martingale_allocation P B A hA φ N hN hNI
  refine ⟨ψ,M,hψ,?_,he,?_⟩
  · intro i
    exact scalar_hedge_self_financing P (W i) 0 (x i) (σ i) r 0 (hx i)
      (volatility_row_normalization A hA i).1.ne' (σ i • ψ i) (M i) (hM i) (hMI i)
  · intro i t w
    exact basket_row_stock_identity P B A hA i (x i) r t w
end Asakura.Chapter12
#print axioms Asakura.Chapter12.basket_allocated_self_financing

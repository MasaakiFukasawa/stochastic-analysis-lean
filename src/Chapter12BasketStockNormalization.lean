import Chapter12VolatilityRowNormalization
import Chapter12ScalarStrategyDomains

open MeasureTheory Set
open scoped BigOperators
namespace Asakura.Chapter12
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter4
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

theorem basket_row_stock_identity {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.det≠0) (i : Fin d) (x r : ℝ) (t : ℝ) (w : Ω) :
    let σ := Real.sqrt (∑ j,A i j^2)
    let W := brownianUnitDirection P B (fun j => A i j/σ) (volatility_row_normalization A hA i).2.2.1
    geometricFlow x r σ ![t,W.W 0 (realTimeClamp t) w]=
      x*Real.exp ((r-(∑ j,A i j^2)/2)*t+∑ j,A i j*B.W j (realTimeClamp t) w) := by
  intro σ W
  simp only [geometricFlow,Matrix.cons_val_zero,Matrix.cons_val_one]
  rw [(volatility_row_normalization A hA i).2.1]
  congr 2
  change _ + σ*(∑ j,(A i j/σ)*B.W j (realTimeClamp t) w)=_
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [←mul_assoc,(volatility_row_normalization A hA i).2.2.2 j]

theorem basket_allocated_holding (σ ψ s r t : ℝ) (hσ : σ≠0) :
    (σ*ψ)/(σ*(Real.exp (-r*t)*s))=ψ/(Real.exp (-r*t)*s) ∧
      (σ*ψ)/σ=ψ := by
  constructor
  · exact mul_div_mul_left ψ _ hσ
  · exact mul_div_cancel_left₀ ψ hσ
end Asakura.Chapter12
#print axioms Asakura.Chapter12.basket_row_stock_identity

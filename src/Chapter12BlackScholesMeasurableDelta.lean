import Chapter12BrownianBasketGreeks
import Chapter12BlackScholesStockNormalization

open MeasureTheory ProbabilityTheory Set Matrix
namespace Asakura.Chapter12
open Asakura.FullAudit Asakura.Chapter4
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

/-- The printed delta formula, with W_T/T and the original volatility
matrix, on the actual Brownian space. The discount is an arbitrary constant. -/
theorem black_scholes_measurable_delta {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ}
    (B : BrownianSystem P (d+1)) (T : ℝ) (hT : 0<T)
    (A : Matrix (Fin (d+1)) (Fin (d+1)) ℝ) (hA : A.det≠0)
    (x b : Fin (d+1) → ℝ) (i : Fin (d+1)) (hx : 0<x i)
    (h : (Fin (d+1) → ℝ) → ℝ) (hm : Measurable h)
    (C : ℝ) (n : ℕ) (hb : ∀ y,|h y|≤C*(1+‖y‖^n)) (discount : ℝ) :
    HasDerivAt (fun u : ℝ => discount*∫ w,h (fun k => (if k=i then u else x k)*
        Real.exp (b k+∑ j,A k j*B.W j (realTimeClamp T) w)) ∂P)
      (discount*∫ w,h (fun k => x k*Real.exp (b k+∑ j,A k j*B.W j (realTimeClamp T) w))*
        (((∑ j,(A⁻¹) j i*B.W j (realTimeClamp T) w)/T)/x i) ∂P) (x i) := by
  classical
  have hd := (brownian_basket_delta P B T hT ((Real.sqrt T) • A)
    (bs_scaled_matrix_nonsingular A hA T hT) x b i hx h hm C n hb).const_mul discount
  dsimp only at hd
  simp_rw [bs_terminal_normalization A T hT,bs_delta_normalization A hA T hT] at hd
  exact hd

end Asakura.Chapter12

import Chapter12BrownianBasketGamma
import Chapter12BlackScholesStockNormalization

open MeasureTheory ProbabilityTheory Set Matrix
namespace Asakura.Chapter12
open Asakura.FullAudit Asakura.Chapter4
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

theorem black_scholes_measurable_gamma {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ}
    (B : BrownianSystem P (d+1)) (T : ℝ) (hT : 0<T)
    (A : Matrix (Fin (d+1)) (Fin (d+1)) ℝ) (hA : A.det≠0)
    (x b : Fin (d+1) → ℝ) (i j : Fin (d+1)) (hxi : 0<x i) (hxj : 0<x j)
    (h : (Fin (d+1) → ℝ) → ℝ) (hm : Measurable h)
    (C : ℝ) (n : ℕ) (hb : ∀ y,|h y|≤C*(1+‖y‖^n)) (discount : ℝ) :
    let L := fun i w => (∑ a,(A⁻¹) a i*B.W a (realTimeClamp T) w)/T
    let Q := fun i j => (∑ a,(A⁻¹) a i*(A⁻¹) a j)/T
    HasDerivAt
      (fun u => discount*((∫ w,h (fun k => (if k=j then u else x k)*
        Real.exp (b k+∑ a,A k a*B.W a (realTimeClamp T) w))*L i w ∂P)/(if i=j then u else x i)))
      (discount*∫ w,h (fun k => x k*Real.exp (b k+∑ a,A k a*B.W a (realTimeClamp T) w))*
        ((L i w*L j w-Q i j-(if i=j then L i w else 0))/(x i*x j)) ∂P) (x j) := by
  classical
  have hd := (brownian_basket_gamma P B T hT ((Real.sqrt T) • A)
    (bs_scaled_matrix_nonsingular A hA T hT) x b i j hxi hxj h hm C n hb).const_mul discount
  dsimp only at hd ⊢
  simp_rw [bs_terminal_normalization A T hT,bs_delta_normalization A hA T hT,
    bs_gamma_normalization A hA T hT] at hd
  exact hd

end Asakura.Chapter12

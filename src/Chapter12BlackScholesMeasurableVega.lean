import Chapter12BrownianBasketGreeks
import Chapter12BlackScholesStockNormalization

open MeasureTheory ProbabilityTheory Set Matrix
namespace Asakura.Chapter12
open Asakura.FullAudit Asakura.Chapter4
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

/-- The printed vega weight: (|W_T|²/T-d)/s-(A⁻¹d₀)·W_T.
The mean correction in the stock and the weight are proved simultaneously. -/
theorem black_scholes_measurable_vega {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ}
    (B : BrownianSystem P (d+1)) (T : ℝ) (hT : 0<T)
    (A : Matrix (Fin (d+1)) (Fin (d+1)) ℝ) (hA : A.det≠0)
    (x b d0 : Fin (d+1) → ℝ)
    (h : (Fin (d+1) → ℝ) → ℝ) (hm : Measurable h)
    (C : ℝ) (n : ℕ) (hb : ∀ y,|h y|≤C*(1+‖y‖^n)) (discount s : ℝ) (hs : 0<s) :
    HasDerivAt (fun u => discount*∫ w,h (fun i => x i*Real.exp
      (b i+u*(∑ j,A i j*B.W j (realTimeClamp T) w)-u^2*T*d0 i/2)) ∂P)
      (discount*∫ w,h (fun i => x i*Real.exp
        (b i+s*(∑ j,A i j*B.W j (realTimeClamp T) w)-s^2*T*d0 i/2))*
        (((∑ i,(B.W i (realTimeClamp T) w)^2)/T-(d+1:ℝ))/s-
          (∑ i,(A⁻¹.mulVec d0) i*B.W i (realTimeClamp T) w)) ∂P) s := by
  have hd := (brownian_basket_vega P B T hT x b
    (fun j => Real.sqrt T*(A⁻¹.mulVec d0) j) ((Real.sqrt T) • A) h hm C n hb s hs).const_mul discount
  dsimp only at hd
  simp_rw [bs_vega_terminal_normalization A hA T _ hT] at hd
  have hw (w : Ω) := bs_vega_score_normalization (d := d+1) T s hT
    (fun i => B.W i (realTimeClamp T) w) (A⁻¹.mulVec d0)
  norm_num only [Nat.cast_add,Nat.cast_one] at hw
  simp_rw [hw] at hd
  simpa only [← add_sub_assoc] using hd

end Asakura.Chapter12

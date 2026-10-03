import Chapter12BasketDeltaMeasurable
import Chapter12BasketGammaMeasurable
import Chapter12BasketVegaMeasurable
import Chapter12BrownianNormalizedLaw
import Chapter12GreekLawTransport

open MeasureTheory ProbabilityTheory Set
namespace Asakura.Chapter12
open Asakura.FullAudit Asakura.Chapter4
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000

/-- The measurable-payoff delta on the actual Brownian probability space. -/
theorem brownian_basket_delta {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ}
    (B : BrownianSystem P (d+1)) (T : ℝ) (hT : 0<T)
    (A : Matrix (Fin (d+1)) (Fin (d+1)) ℝ) (hA : A.det≠0)
    (x b : Fin (d+1) → ℝ) (i : Fin (d+1)) (hx : 0<x i)
    (h : (Fin (d+1) → ℝ) → ℝ) (hm : Measurable h)
    (C : ℝ) (n : ℕ) (hb : ∀ y,|h y|≤C*(1+‖y‖^n)) :
    let Z := fun w j => B.W j (realTimeClamp T) w/Real.sqrt T
    HasDerivAt (fun u : ℝ => ∫ w,h (fun k => (if k=i then u else x k)*
        Real.exp (b k+∑ j,A k j*Z w j)) ∂P)
      (∫ w,h (fun k => x k*Real.exp (b k+∑ j,A k j*Z w j))*
        ((∑ j,(A⁻¹) j i*Z w j)/x i) ∂P) (x i) := by
  classical
  dsimp only
  refine greek_derivative_transport P _ _ (actual_brownian_normalized_terminal_law P B T hT)
    (fun u z => h (fun k => (if k=i then u else x k)*Real.exp (b k+∑ j,A k j*z j))) ?_
    (fun z => h (fun k => x k*Real.exp (b k+∑ j,A k j*z j))*((∑ j,(A⁻¹) j i*z j)/x i)) ?_ (x i) ?_
  · intro u
    exact hm.comp (by fun_prop)
  · exact (hm.comp (by fun_prop)).mul (by fun_prop)
  · exact basket_measurable_delta A hA x b i hx h hm C n hb

/-- Proportional-volatility vega, transported to the actual Brownian
terminal coordinates by their proved joint Gaussian law. -/
theorem brownian_basket_vega {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ}
    (B : BrownianSystem P (d+1)) (T : ℝ) (hT : 0<T)
    (x b k : Fin (d+1) → ℝ) (A : Matrix (Fin (d+1)) (Fin (d+1)) ℝ)
    (h : (Fin (d+1) → ℝ) → ℝ) (hm : Measurable h)
    (C : ℝ) (n : ℕ) (hb : ∀ y,|h y|≤C*(1+‖y‖^n)) (s : ℝ) (hs : 0<s) :
    let Z := fun w j => B.W j (realTimeClamp T) w/Real.sqrt T
    HasDerivAt (fun u => ∫ w,h (fun i => x i*Real.exp
      (b i+∑ j,A i j*(u*Z w j-u^2*k j/2))) ∂P)
      (∫ w,h (fun i => x i*Real.exp (b i+∑ j,A i j*(s*Z w j-s^2*k j/2)))*
        (((∑ i,(Z w i)^2)-(d+1:ℝ))/s-(∑ i,k i*Z w i)) ∂P) s := by
  dsimp only
  have hd := basket_vega_measurable x b k A h hm C n hb s hs
  norm_num only [Nat.cast_add,Nat.cast_one] at hd
  refine greek_derivative_transport P _ _ (actual_brownian_normalized_terminal_law P B T hT)
    (fun u z => h (fun i => x i*Real.exp (b i+∑ j,A i j*(u*z j-u^2*k j/2)))) ?_
    (fun z => h (fun i => x i*Real.exp (b i+∑ j,A i j*(s*z j-s^2*k j/2)))*
      (((∑ i,(z i)^2)-(d+1:ℝ))/s-(∑ i,k i*z i))) ?_ s ?_
  · intro u
    exact hm.comp (by fun_prop)
  · exact (hm.comp (by fun_prop)).mul (by fun_prop)
  · exact hd

end Asakura.Chapter12

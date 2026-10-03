import Chapter12ConditionalFiniteCombination
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

open MeasureTheory
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

theorem discounted_basket_holding_identity (r T t S w C : ℝ) (hS : S≠0) :
    (Real.exp (-r*t)*S)*(Real.exp (-r*(T-t))*w/S*C)=Real.exp (-r*T)*w*C := by
  have he : Real.exp (-r*t)*Real.exp (-r*(T-t))=Real.exp (-r*T) := by
    rw [←Real.exp_add]
    congr 1
    ring
  field_simp
  simp only [neg_mul] at he
  rw [he]
  ring

/-- Conditional linearity turns the Clark integrand into the printed stock
holdings. The resulting matrix equation matches every Brownian direction. -/
theorem basket_clark_holdings_coefficient {Ω ι : Type*} [m : MeasurableSpace Ω]
    [Fintype ι] [DecidableEq ι]
    (P : Measure Ω) (F : MeasurableSpace Ω) (A : Matrix ι ι ℝ)
    (r T t : ℝ) (wgt : ι → ℝ) (S : ι → Ω → ℝ) (hS : ∀ i w,S i w≠0)
    (X : ι → Ω → ℝ) (hX : ∀ i,Integrable (X i) P)
    (φ : ι → Ω → ℝ)
    (hφ : ∀ j,φ j =ᵐ[P] P[(fun w => ∑ i,(Real.exp (-r*T)*A i j*wgt i)*X i w)|F]) :
    ∀ᵐ w ∂P,∀ j,
      (∑ i,A i j*((Real.exp (-r*t)*S i w)*
        (Real.exp (-r*(T-t))*wgt i/S i w*P[X i|F] w)))=φ j w := by
  letI : MeasurableSpace Ω := m
  have hc := fun j => conditional_finite_linear_combination P F
    (fun i => Real.exp (-r*T)*A i j*wgt i) X hX
  filter_upwards [ae_all_iff.mpr hφ,ae_all_iff.mpr hc] with w hw hh
  intro j
  rw [hw j,hh j]
  apply Finset.sum_congr rfl
  intro i _
  rw [discounted_basket_holding_identity r T t (S i w) (wgt i) (P[X i|F] w) (hS i w)]
  ring

end Asakura.Chapter12

import Chapter10MomentEquation
import Chapter10LinearCrossMoment

open MeasureTheory Matrix
open scoped BigOperators
namespace Asakura.Chapter10
set_option backward.isDefEq.respectTransparency false

/-- The integral form of the covariance ODE, obtained from the coordinate Ito
product identity. All moment functions below are defined as actual integrals. -/
theorem covariance_integral_equation {Ω S τ ι : Type*} [m : MeasurableSpace Ω]
    [MeasurableSpace S] [Preorder τ] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (ν : Measure S) [SFinite ν]
    (F : Filtration τ m) (M : τ → Ω → ℝ) (hM : Martingale M F P)
    (s t : τ) (hst : s≤t) (hzero : M s =ᵐ[P] 0)
    (e₀ eT : ι → Ω → ℝ) (h₀ : ∀ i,MemLp (e₀ i) 2 P)
    (e : S → ι → Ω → ℝ) (he : ∀ u i,MemLp (e u i) 2 P)
    (A Q : S → Matrix ι ι ℝ) (i j : ι)
    (hH : Integrable (fun z : Ω × S =>
      ((A z.2)*ᵥ(fun k => e z.2 k z.1)) i*e z.2 j z.1+
      e z.2 i z.1*((A z.2)*ᵥ(fun k => e z.2 k z.1)) j+Q z.2 i j) (P.prod ν))
    (hid : (fun w => eT i w*eT j w) =ᵐ[P] (fun w => e₀ i w*e₀ j w+
      (∫ u,((A u)*ᵥ(fun k => e u k w)) i*e u j w+
        e u i w*((A u)*ᵥ(fun k => e u k w)) j+Q u i j ∂ν)+M t w)) :
    let V : S → Matrix ι ι ℝ := fun u k l => ∫ w,e u k w*e u l w ∂P
    (∫ w,eT i w*eT j w ∂P)=(∫ w,e₀ i w*e₀ j w ∂P)+
      ∫ u,(A u*V u+V u*(A u).transpose+Q u) i j ∂ν := by
  dsimp only
  have hh := expectation_of_ito_identity P ν F M hM s t hst hzero
    (fun w => e₀ i w*e₀ j w) (fun w => eT i w*eT j w)
    ((h₀ i).integrable_mul (h₀ j)) _ hH hid
  rw [hh.2]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun u => covariance_drift_expectation P (e u) (he u) (A u) (Q u) i j)

end Asakura.Chapter10

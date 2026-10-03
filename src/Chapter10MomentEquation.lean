import Mathlib.Probability.Martingale.Basic
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory Set Filter
namespace Asakura.Chapter10
set_option backward.isDefEq.respectTransparency false

/-- Taking expectations of an Ito product identity. The martingale term is
removed from its actual conditional-expectation property, and the drift is
exchanged by Fubini, including the required integrability of the endpoint. -/
theorem expectation_of_ito_identity {Ω S ι : Type*} [m : MeasurableSpace Ω]
    [MeasurableSpace S] [Preorder ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (ν : Measure S) [SFinite ν]
    (F : Filtration ι m) (M : ι → Ω → ℝ) (hM : Martingale M F P)
    (s t : ι) (hst : s≤t) (hzero : M s =ᵐ[P] 0)
    (Z X : Ω → ℝ) (hZ : Integrable Z P)
    (H : Ω × S → ℝ) (hH : Integrable H (P.prod ν))
    (hid : X =ᵐ[P] (fun w => Z w+(∫ u,H (w,u) ∂ν)+M t w)) :
    Integrable X P ∧
      (∫ w,X w ∂P)=(∫ w,Z w ∂P)+∫ u,(∫ w,H (w,u) ∂P) ∂ν := by
  have hMt : (∫ w,M t w ∂P)=0 := by
    calc
      _ = ∫ w,P[M t|F s] w ∂P := (integral_condExp (F.le s)).symm
      _ = ∫ w,M s w ∂P := integral_congr_ae (hM.condExp_ae_eq hst)
      _ = 0 := by rw [integral_congr_ae hzero]; simp
  have hi := (hZ.add hH.integral_prod_left).add (hM.integrable t)
  refine ⟨hi.congr hid.symm,?_⟩
  rw [integral_congr_ae hid,integral_add (show Integrable (fun w => Z w+∫ u,H (w,u) ∂ν) P from hZ.add hH.integral_prod_left) (hM.integrable t),
    integral_add hZ hH.integral_prod_left,hMt,add_zero]
  rw [integral_integral_swap (f := fun w u => H (w,u)) hH]

end Asakura.Chapter10

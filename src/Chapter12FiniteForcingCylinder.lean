import Chapter12FiniteForcingAllOrders
import Chapter12PositiveBoundsGrowth
import Chapter12CylinderFromSmooth

open MeasureTheory Set
open scoped Topology ContDiff NNReal
namespace Asakura.Chapter12
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

theorem finite_forcing_cylinder {E H : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (b : E → E) (hb : ContDiff ℝ ∞ b)
    (hbound : ∀k:ℕ,1≤k → ∃C:ℝ≥0,∀x,‖iteratedFDeriv ℝ k b x‖≤(C:ℝ))
    (T : ℝ) (hT : 0≤T) (a : C(Icc (0:ℝ) T,E)) (n : ℕ)
    (R : C(Icc (0:ℝ) T,(Fin n → ℝ) →L[ℝ] E))
    (ell : E →L[ℝ] ℝ) (u : Fin n → H) :
    ∃X : (Fin n → ℝ) → C(Icc (0:ℝ) T,E),
      (∀z t,X z t=a t+R t z+∫s in 0..t.val,b (X z (projIcc 0 T hT s))) ∧
      ∀t,∃c : SmoothCylinder H,c.dim=n ∧ HEq c.direction u ∧
        HEq c.f (fun z => ell (X z t)) := by
  obtain ⟨X,hX,heq,hbX⟩ := finite_forcing_all_orders b hb hbound T hT a R
  refine ⟨X,heq,?_⟩
  intro t
  let L : C(Icc (0:ℝ) T,E) →L[ℝ] ℝ := ell.comp (ContinuousMap.evalCLM ℝ t)
  have hLg : ∀k:ℕ,1≤k → ∃C:ℝ,0≤C ∧ ∀x,‖iteratedFDeriv ℝ k L x‖≤C := by
    simpa only [zero_add] using affine_all_higher_bounds L 0
  have hg := all_higher_bounds_comp X L hX L.contDiff hbX hLg
  have hp := positive_derivative_bounds_polynomial (L ∘ X) (L.contDiff.comp hX) hg
  exact ⟨smoothCylinderOfFunction u (L ∘ X) (L.contDiff.comp hX) hp,rfl,HEq.rfl,HEq.rfl⟩
end Asakura.Chapter12
#print axioms Asakura.Chapter12.finite_forcing_cylinder

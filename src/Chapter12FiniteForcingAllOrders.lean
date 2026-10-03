import Chapter12SmoothForcingAllBounds
import Chapter12BoundedHigherComposition
import Chapter12AffineHigherBounds

open MeasureTheory Set
open scoped Topology ContDiff NNReal
namespace Asakura.Chapter12
universe u
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

theorem finite_forcing_all_orders {E G : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (b : E → E) (hb : ContDiff ℝ ∞ b)
    (hbound : ∀k:ℕ,1≤k → ∃C:ℝ≥0,∀x,‖iteratedFDeriv ℝ k b x‖≤(C:ℝ))
    (T : ℝ) (hT : 0≤T) (a : C(Icc (0:ℝ) T,E))
    (R : C(Icc (0:ℝ) T,G →L[ℝ] E)) :
    ∃X : G → C(Icc (0:ℝ) T,E),ContDiff ℝ ∞ X ∧
      (∀z t,X z t=a t+R t z+∫s in 0..t.val,b (X z (projIcc 0 T hT s))) ∧
      ∀k:ℕ,1≤k → ∃C:ℝ,0≤C ∧ ∀z,‖iteratedFDeriv ℝ k X z‖≤C := by
  obtain ⟨S,hS,heq,hSb⟩ := smooth_forcing_all_bounds b hb hbound T hT
  let L : G →L[ℝ] C(Icc (0:ℝ) T,E) := (continuousMapApply R).comp (ContinuousLinearMap.const ℝ (Icc (0:ℝ) T))
  let Q : G → C(Icc (0:ℝ) T,E) := fun z => a+L z
  have hQ : ContDiff ℝ ∞ Q := contDiff_const.add L.contDiff
  refine ⟨S ∘ Q,hS.comp hQ,?_,all_higher_bounds_comp Q S hQ hS (affine_all_higher_bounds L a) hSb⟩
  intro z t
  exact heq (Q z) t
end Asakura.Chapter12
#print axioms Asakura.Chapter12.finite_forcing_all_orders

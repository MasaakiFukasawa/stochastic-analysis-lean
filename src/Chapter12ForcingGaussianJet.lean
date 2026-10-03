import Chapter12SmoothForcingAllBounds
import Chapter12PositiveBoundsGrowth
import Chapter12GaussianJets
import Chapter12BoundedHigherComposition

open MeasureTheory Set
open scoped Topology ContDiff NNReal
namespace Asakura.Chapter12
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

theorem forcing_gaussian_jet {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (T : ℝ) (S : C(Icc (0:ℝ) T,E) → C(Icc (0:ℝ) T,E))
    (hS : ContDiff ℝ ∞ S)
    (hSB : ∀k:ℕ,1≤k → ∃C:ℝ,0≤C ∧ ∀q,‖iteratedFDeriv ℝ k S q‖≤C)
    (n : ℕ) (L : (Fin n → ℝ) →L[ℝ] C(Icc (0:ℝ) T,E))
    (a : C(Icc (0:ℝ) T,E)) (ell : E →L[ℝ] ℝ) (t : Icc (0:ℝ) T) :
    ∃f : GaussianJet n,f.f=fun z => ell (S (a+L z) t) := by
  let Q := fun z => a+L z
  let R : C(Icc (0:ℝ) T,E) →L[ℝ] ℝ := ell.comp (ContinuousMap.evalCLM ℝ t)
  have hQ : ContDiff ℝ ∞ Q := contDiff_const.add L.contDiff
  have hQB := affine_all_higher_bounds L a
  have hX := all_higher_bounds_comp Q S hQ hS hQB hSB
  have hR : ∀k:ℕ,1≤k → ∃C:ℝ,0≤C ∧ ∀x,‖iteratedFDeriv ℝ k R x‖≤C := by
    simpa only [zero_add] using affine_all_higher_bounds R 0
  have hF := all_higher_bounds_comp (S ∘ Q) R (hS.comp hQ) R.contDiff hX hR
  exact ⟨⟨R ∘ S ∘ Q,R.contDiff.comp (hS.comp hQ),
    positive_derivative_bounds_polynomial _ (R.contDiff.comp (hS.comp hQ)) hF⟩,rfl⟩
end Asakura.Chapter12
#print axioms Asakura.Chapter12.forcing_gaussian_jet

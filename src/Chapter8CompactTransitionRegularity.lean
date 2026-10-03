import Chapter8ConstructedTransitionC2
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Normed.Group.Bounded

open MeasureTheory Set
open scoped NNReal Topology ContDiff
namespace Asakura.Chapter8
attribute [local instance] nestedOpNormed nestedOpSpace nestedBiNormed nestedBiSpace
attribute [local instance] scalarOpNormed scalarOpSpace scalarBiNormed scalarBiSpace
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

/-- The spatial regularity step in the Gibbs proof, for exactly the
smooth compactly supported test functions used there. Bounds on the
first two drift derivatives yield all required flow regularity. -/
theorem compact_transition_regularity {E Ω : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (b : E → E) (D : E → E →L[ℝ] E) (D₂ : E → E →L[ℝ] E →L[ℝ] E)
    (hD : ∀ z,HasFDerivAt b (D z) z) (hD₂ : ∀ z,HasFDerivAt D (D₂ z) z)
    (hcD₂ : Continuous D₂) (C L : ℝ≥0) (hL : 0<L)
    (hDb : ∀ z,‖D z‖ ≤ (L:ℝ)) (hD₂b : ∀ z,‖D₂ z‖ ≤ (C:ℝ))
    (T : ℝ) (hT : 0 ≤ T) (V : Ω → C(Icc (0:ℝ) T,E)) (hV : Measurable V)
    (f : E → ℝ) (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) :
    ∃ S : E × C(Icc (0:ℝ) T,E) → C(Icc (0:ℝ) T,E),Continuous S ∧
      (∀ p t,S p t=p.1+(∫ s in 0..t.val,b (S p (projIcc 0 T hT s)))+p.2 t) ∧
      ∀ t : Icc (0:ℝ) T,ContDiff ℝ 2 (fun x => ∫ η,f (S (x,V η) t) ∂P) := by
  have hDC : LipschitzWith C D := by
    apply lipschitzWith_of_nnnorm_fderiv_le (fun z => (hD₂ z).differentiableAt)
    intro z
    rw [(hD₂ z).fderiv]
    exact_mod_cast hD₂b z
  have hf1 : ContDiff ℝ ∞ (fderiv ℝ f) := (contDiff_infty_iff_fderiv.mp hf).2
  have hf2 : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ f)) := (contDiff_infty_iff_fderiv.mp hf1).2
  obtain ⟨B₀,hB₀⟩ := hs.exists_bound_of_continuous hf.continuous
  obtain ⟨B₁,hB₁⟩ := (hs.fderiv ℝ).exists_bound_of_continuous hf1.continuous
  obtain ⟨B₂,hB₂⟩ := ((hs.fderiv ℝ).fderiv ℝ).exists_bound_of_continuous hf2.continuous
  exact constructed_transition_C2 P b D D₂ hD hD₂ hcD₂ C L hDC hL hDb T hT V hV
    f (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f))
    (fun z => (hf.differentiable (by simp)).differentiableAt.hasFDerivAt)
    (fun z => (hf1.differentiable (by simp)).differentiableAt.hasFDerivAt)
    hf2.continuous B₀ (max B₁ 0) (max B₂ 0) (le_max_right _ _) (le_max_right _ _) hB₀
    (fun z => (hB₁ z).trans (le_max_left _ _)) (fun z => (hB₂ z).trans (le_max_left _ _))

end Asakura.Chapter8

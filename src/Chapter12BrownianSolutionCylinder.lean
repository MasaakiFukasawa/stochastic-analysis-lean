import Chapter12BrownianSolutionCylinderFrames

open MeasureTheory Set
open scoped ContDiff
namespace Asakura.Chapter12
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

theorem brownian_solution_cylinder {Ω : Type*} {E : Type} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (P : Measure Ω) (d : ℕ) (T : ℝ) (hT : 0<T)
    (W : FiniteWienerHilbert d T →ₗᵢ[ℝ] Lp ℝ 2 P)
    (B : BrownianTimeCoordinates d T → Ω → ℝ)
    (hB : ∀z,B z=ᵐ[P] (W (brownianTimeDirection z) : Ω → ℝ))
    (v : Fin (d+1) → E) (x : E)
    (S : C(Icc (0:ℝ) T,E) → C(Icc (0:ℝ) T,E)) (hS : ContDiff ℝ ∞ S)
    (hSB : ∀k:ℕ,1≤k → ∃C:ℝ,0≤C ∧ ∀q,‖iteratedFDeriv ℝ k S q‖≤C)
    (ell : E →L[ℝ] ℝ) (t : Icc (0:ℝ) T)
    (h : ℝ) (hh : 0<h) (n : ℕ) (hnT : (n:ℝ)*h=T) :
    ∃c : SmoothCylinder (FiniteWienerHilbert d T),c.value P W=ᵐ[P]
      (fun w => ell (S (ContinuousMap.const _ x+brownianPolygonalForcing d T hT.le B v h n w) t)) := by
  obtain ⟨m,e,he,f,g,hff,hgf,hfv,hgv⟩ := brownian_solution_cylinder_frames P d T hT W B hB v x
    S hS hSB ell t h h hh hh n n hnT hnT
  exact ⟨f.toCylinder e,hfv⟩
end Asakura.Chapter12
#print axioms Asakura.Chapter12.brownian_solution_cylinder

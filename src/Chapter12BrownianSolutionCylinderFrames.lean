import Chapter12BrownianForcingFrames
import Chapter12ForcingGaussianRepresentation

open MeasureTheory Set
open scoped ContDiff
namespace Asakura.Chapter12
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

theorem brownian_solution_cylinder_frames {Ω : Type*} {E : Type} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (P : Measure Ω) (d : ℕ) (T : ℝ) (hT : 0<T)
    (W : FiniteWienerHilbert d T →ₗᵢ[ℝ] Lp ℝ 2 P)
    (B : BrownianTimeCoordinates d T → Ω → ℝ)
    (hB : ∀z,B z=ᵐ[P] (W (brownianTimeDirection z) : Ω → ℝ))
    (v : Fin (d+1) → E) (x : E)
    (S : C(Icc (0:ℝ) T,E) → C(Icc (0:ℝ) T,E)) (hS : ContDiff ℝ ∞ S)
    (hSB : ∀k:ℕ,1≤k → ∃C:ℝ,0≤C ∧ ∀q,‖iteratedFDeriv ℝ k S q‖≤C)
    (ell : E →L[ℝ] ℝ) (t : Icc (0:ℝ) T)
    (h h' : ℝ) (hh : 0<h) (hh' : 0<h') (n n' : ℕ)
    (hnT : (n:ℝ)*h=T) (hnT' : (n':ℝ)*h'=T) :
    ∃m:ℕ,∃e:Fin (m+1) → FiniteWienerHilbert d T,Orthonormal ℝ e ∧
      ∃f g : GaussianJet (m+1),
      (f.f=fun z => ell (S (ContinuousMap.const _ x+
        kernelForcingPath e (fun i => brownianKernelPolygonal d T i h n) v z) t)) ∧
      (g.f=fun z => ell (S (ContinuousMap.const _ x+
        kernelForcingPath e (fun i => brownianKernelPolygonal d T i h' n') v z) t)) ∧
      (f.toCylinder e).value P W=ᵐ[P]
        (fun w => ell (S (ContinuousMap.const _ x+brownianPolygonalForcing d T hT.le B v h n w) t)) ∧
      (g.toCylinder e).value P W=ᵐ[P]
        (fun w => ell (S (ContinuousMap.const _ x+brownianPolygonalForcing d T hT.le B v h' n' w) t)) := by
  obtain ⟨m,e,he,hf,hg⟩ := brownian_forcing_frames P d T hT W B hB v h h' hh hh' n n' hnT hnT'
  obtain ⟨f,hff,hfv⟩ := forcing_gaussian_representation _ P W T S hS hSB (m+1) e _
    (ContinuousMap.const _ x) ell t _ hf
  obtain ⟨g,hgf,hgv⟩ := forcing_gaussian_representation _ P W T S hS hSB (m+1) e _
    (ContinuousMap.const _ x) ell t _ hg
  exact ⟨m,e,he,f,g,hff,hgf,hfv,hgv⟩
end Asakura.Chapter12
#print axioms Asakura.Chapter12.brownian_solution_cylinder_frames

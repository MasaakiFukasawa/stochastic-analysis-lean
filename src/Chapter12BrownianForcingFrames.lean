import Chapter12BrownianPolygonalFrames
import Chapter12KernelForcingRepresentation
import Chapter12ConstructedPolygonalConvergence

open MeasureTheory Set
namespace Asakura.Chapter12
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

noncomputable def brownianPolygonalForcing {Ω E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (d : ℕ) (T : ℝ) (hT : 0≤T) (X : BrownianTimeCoordinates d T → Ω → ℝ)
    (v : Fin (d+1) → E) (h : ℝ) (n : ℕ) (w : Ω) : C(Icc (0:ℝ) T,E) :=
  ∑i,⟨fun t => polygonalPath (fun s => X (i,projIcc 0 T hT s) w) h n t.val • v i,
    ((polygonalPath_continuous _ h n).comp continuous_subtype_val).smul continuous_const⟩

theorem brownian_forcing_frames {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : Measure Ω) (d : ℕ) (T : ℝ) (hT : 0<T)
    (W : FiniteWienerHilbert d T →ₗᵢ[ℝ] Lp ℝ 2 P)
    (X : BrownianTimeCoordinates d T → Ω → ℝ)
    (hX : ∀z,X z=ᵐ[P] (W (brownianTimeDirection z) : Ω → ℝ))
    (v : Fin (d+1) → E) (h h' : ℝ) (hh : 0<h) (hh' : 0<h') (n n' : ℕ)
    (hnT : (n:ℝ)*h=T) (hnT' : (n':ℝ)*h'=T) :
    ∃m:ℕ,∃e:Fin (m+1) → FiniteWienerHilbert d T,Orthonormal ℝ e ∧
      (∀ᵐw ∂P,kernelForcingPath e (fun i => brownianKernelPolygonal d T i h n) v
        (fun j => W (e j) w)=brownianPolygonalForcing d T hT.le X v h n w) ∧
      (∀ᵐw ∂P,kernelForcingPath e (fun i => brownianKernelPolygonal d T i h' n') v
        (fun j => W (e j) w)=brownianPolygonalForcing d T hT.le X v h' n' w) := by
  obtain ⟨m,e,he,hf,hg⟩ := brownian_polygonal_frames P d T hT W X hX h h' hh hh' n n' hnT hnT'
  refine ⟨m,e,he,?_,?_⟩
  · filter_upwards [hf] with w hw
    exact kernel_forcing_representation e _ v _
      (fun i => polygonalCompact (fun s => X (i,projIcc 0 T hT.le s) w) T h n) hw
  · filter_upwards [hg] with w hw
    exact kernel_forcing_representation e _ v _
      (fun i => polygonalCompact (fun s => X (i,projIcc 0 T hT.le s) w) T h' n') hw
end Asakura.Chapter12
#print axioms Asakura.Chapter12.brownian_forcing_frames

import Chapter12BrownianPolygonalHilbertFrames
import Chapter12BrownianForcingFrames
import Chapter12HilbertKernelFactorization
import Chapter12KernelForcingRepresentation
import Chapter12ConstructedPolygonalConvergence

open MeasureTheory Set
namespace Asakura.Chapter12
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

theorem brownian_forcing_hilbert_frames {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : Measure Ω) (d : ℕ) (T : ℝ) (hT : 0<T)
    (W : FiniteWienerHilbert d T →ₗᵢ[ℝ] Lp ℝ 2 P)
    (X : BrownianTimeCoordinates d T → Ω → ℝ)
    (hX : ∀z,X z=ᵐ[P] (W (brownianTimeDirection z) : Ω → ℝ))
    (v : Fin (d+1) → E) (h h' : ℝ) (hh : 0<h) (hh' : 0<h') (n n' : ℕ)
    (hnT : (n:ℝ)*h=T) (hnT' : (n':ℝ)*h'=T) :
    ∃m:ℕ,∃e:Fin (m+1) → FiniteWienerHilbert d T,Orthonormal ℝ e ∧
      hilbertKernelForcing (fun i => brownianKernelPolygonal d T i h n) v=
        (kernelForcingPath e (fun i => brownianKernelPolygonal d T i h n) v).comp (hilbertCoordinates e) ∧
      hilbertKernelForcing (fun i => brownianKernelPolygonal d T i h' n') v=
        (kernelForcingPath e (fun i => brownianKernelPolygonal d T i h' n') v).comp (hilbertCoordinates e) ∧
      (∀ᵐw ∂P,kernelForcingPath e (fun i => brownianKernelPolygonal d T i h n) v
        (fun j => W (e j) w)=brownianPolygonalForcing d T hT.le X v h n w) ∧
      (∀ᵐw ∂P,kernelForcingPath e (fun i => brownianKernelPolygonal d T i h' n') v
        (fun j => W (e j) w)=brownianPolygonalForcing d T hT.le X v h' n' w) := by
  obtain ⟨m,e,he,hK,hK',hf,hg⟩ := brownian_polygonal_hilbert_frames P d T hT W X hX h h' hh hh' n n' hnT hnT'
  refine ⟨m,e,he,hilbert_kernel_factorization e _ v hK,
    hilbert_kernel_factorization e _ v hK',?_,?_⟩
  · filter_upwards [hf] with w hw
    exact kernel_forcing_representation e _ v _
      (fun i => polygonalCompact (fun s => X (i,projIcc 0 T hT.le s) w) T h n) hw
  · filter_upwards [hg] with w hw
    exact kernel_forcing_representation e _ v _
      (fun i => polygonalCompact (fun s => X (i,projIcc 0 T hT.le s) w) T h' n') hw
end Asakura.Chapter12
#print axioms Asakura.Chapter12.brownian_forcing_hilbert_frames

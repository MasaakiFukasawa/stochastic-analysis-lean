import Chapter12TwoPolygonalWienerFrames
import Chapter12BrownianKernelPolygonal

open MeasureTheory Set
open scoped Topology
namespace Asakura.Chapter12
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

theorem brownian_polygonal_hilbert_frames {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (d : ℕ) (T : ℝ) (hT : 0<T)
    (W : FiniteWienerHilbert d T →ₗᵢ[ℝ] Lp ℝ 2 P)
    (X : BrownianTimeCoordinates d T → Ω → ℝ)
    (hX : ∀z,X z=ᵐ[P] (W (brownianTimeDirection z) : Ω → ℝ))
    (h h' : ℝ) (hh : 0<h) (hh' : 0<h') (n n' : ℕ)
    (hnT : (n:ℝ)*h=T) (hnT' : (n':ℝ)*h'=T) :
    ∃m:ℕ,∃e:Fin (m+1) → FiniteWienerHilbert d T,Orthonormal ℝ e ∧
      (∀i t,brownianKernelPolygonal d T i h n t=∑j,inner ℝ (e j) (brownianKernelPolygonal d T i h n t) • e j) ∧
      (∀i t,brownianKernelPolygonal d T i h' n' t=∑j,inner ℝ (e j) (brownianKernelPolygonal d T i h' n' t) • e j) ∧
      (∀ᵐw ∂P,∀i (t : Icc (0:ℝ) T),polygonalPath (fun s => X (i,projIcc 0 T hT.le s) w) h n t.val=
        ∑j,inner ℝ (e j) (brownianKernelPolygonal d T i h n t)*W (e j) w) ∧
      (∀ᵐw ∂P,∀i (t : Icc (0:ℝ) T),polygonalPath (fun s => X (i,projIcc 0 T hT.le s) w) h' n' t.val=
        ∑j,inner ℝ (e j) (brownianKernelPolygonal d T i h' n' t)*W (e j) w) := by
  letI := finite_horizon_L2_nontrivial T hT
  let f : Fin (d+1) → ℝ → FiniteWienerHilbert d T := fun i s =>
    singleCoordinateIsometry i (finiteTimeIntervalVector T 0 s)
  let Z := fun (i : Fin (d+1)) s => X (i,projIcc 0 T hT.le s)
  have hgrid (q : ℝ) (hq : 0<q) (N : ℕ) (hNT : (N:ℝ)*q=T) (i : Fin (d+1)) (j : Fin (N+1)) :
      Z i ((j:ℝ)*q)=ᵐ[P] (W (f i ((j:ℝ)*q)) : Ω → ℝ) := by
    have hj0 : 0≤(j:ℝ)*q := mul_nonneg (by positivity) hq.le
    have hjT : (j:ℝ)*q≤T := by
      rw [←hNT]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_of_lt_succ j.isLt) hq.le
    have hp := projIcc_of_mem hT.le (show (j:ℝ)*q∈Icc 0 T from ⟨hj0,hjT⟩)
    have hx := hX (i,⟨(j:ℝ)*q,hj0,hjT⟩)
    dsimp only [Z]
    rw [hp]
    exact hx
  obtain ⟨m,e,he,href,href',hrep,hrep'⟩ := two_polygonal_wiener_frames P W f Z h h' n n'
    (hgrid h hh n hnT) (hgrid h' hh' n' hnT')
  have hpoly (i : Fin (d+1)) q N (t : Icc (0:ℝ) T) :
      polygonalPath (f i) q N t.val=brownianKernelPolygonal d T i q N t := by
    let J := singleCoordinateIsometry (H:=Lp ℝ 2 ((volume.restrict (Ioi (0:ℝ))).restrict (Iic T))) i
    exact (linear_polygonal_commutation J.toContinuousLinearMap (fun s => finiteTimeIntervalVector T 0 s) q N t.val).symm
  refine ⟨m,e,he,?_,?_,?_,?_⟩
  · intro i t
    simpa only [hpoly i h n t] using href i t.val
  · intro i t
    simpa only [hpoly i h' n' t] using href' i t.val
  · filter_upwards [hrep] with w hw
    intro i t
    simpa only [Z,hpoly i h n t] using hw i t.val
  · filter_upwards [hrep'] with w hw
    intro i t
    simpa only [Z,hpoly i h' n' t] using hw i t.val
end Asakura.Chapter12
#print axioms Asakura.Chapter12.brownian_polygonal_hilbert_frames

import Chapter12VectorCylinderRebasis

open MeasureTheory Set
namespace Asakura.Chapter12
open Asakura.FullAudit
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

theorem scalar_cylinders_common_frame {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Nontrivial H]
    (P : Measure Ω) (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) {q : ℕ} (c : Fin q → SmoothCylinder H) :
    ∃n:ℕ,∃e:Fin (n+1) → H,∃f:Fin q → GaussianJet (n+1),Orthonormal ℝ e ∧
      ∀i,(c i).value P W=ᵐ[P] ((f i).toCylinder e).value P W := by
  classical
  let dirs : (Σi:Fin q,Fin (c i).dim) → H := fun ij => (c ij.1).direction ij.2
  obtain ⟨n,e,a,he,ha⟩ := finite_common_orthonormal dirs
  let L := fun i => cylinderCoordinateMap (fun j : Fin (c i).dim => a ⟨i,j⟩)
  let f := fun i => (c i).coordinateJet.compLinear (L i)
  refine ⟨n,e,f,he,?_⟩
  intro i
  have hx (j : Fin (c i).dim) : (W ((c i).direction j) : Ω → ℝ)=ᵐ[P]
      (fun w => ∑k,a ⟨i,j⟩ k*W (e k) w) := by
    have hh := ha ⟨i,j⟩
    change (c i).direction j=_ at hh
    rw [hh]
    exact wiener_finite_linearity P W.toLinearMap e _
  filter_upwards [ae_all_iff.mpr hx] with w hw
  change (c i).f (fun j => W ((c i).direction j) w)=(c i).f (L i (fun j => W (e j) w))
  congr 1
  funext j
  exact (hw j).trans (cylinder_coordinate_map_apply (fun j : Fin (c i).dim => a ⟨i,j⟩) (fun j => W (e j) w) j).symm
end Asakura.Chapter12
#print axioms Asakura.Chapter12.scalar_cylinders_common_frame

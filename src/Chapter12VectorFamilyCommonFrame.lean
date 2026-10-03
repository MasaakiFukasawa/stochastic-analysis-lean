import Chapter12VectorCylinderRebasis

open MeasureTheory ProbabilityTheory Set
namespace Asakura.Chapter12
open Asakura.FullAudit
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4500000

theorem vector_family_common_frame {Ω H I : Type*} [MeasurableSpace Ω] [Fintype I]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Nontrivial H]
    (P : Measure Ω) (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (q : I → ℕ)
    (c : ∀i,Fin (q i) → SmoothCylinder H) (v : ∀i,Fin (q i) → H) :
    ∃(n:ℕ) (e:Fin (n+1) → H) (u:I → Fin (n+1) → GaussianJet (n+1)),
      Orthonormal ℝ e ∧ ∀i,
      (fun w => ∑j,(c i j).value P W w • v i j)=ᵐ[P]
        (fun w => ∑j,(u i j).f (fun l => W (e l) w) • e j) := by
  classical
  let dirs : ((Σ i:I,Σ j:Fin (q i),Fin (c i j).dim) ⊕ (Σ i:I,Fin (q i))) → H :=
    Sum.elim (fun ijl => (c ijl.1 ijl.2.1).direction ijl.2.2) (fun ij => v ij.1 ij.2)
  obtain ⟨n,e,a,he,ha⟩ := finite_common_orthonormal dirs
  let L := fun i j => cylinderCoordinateMap (fun l : Fin (c i j).dim => a (Sum.inl ⟨i,j,l⟩))
  let u := fun i l => GaussianJet.finsetSum Finset.univ (fun j : Fin (q i) =>
    (((c i j).coordinateJet).compLinear (L i j)).smul (a (Sum.inr ⟨i,j⟩) l))
  refine ⟨n,e,u,he,fun i => ?_⟩
  have hx (j:Fin (q i)) (l:Fin (c i j).dim) :
      (W ((c i j).direction l) : Ω → ℝ)=ᵐ[P]
        (fun w => ∑m,a (Sum.inl ⟨i,j,l⟩) m*W (e m) w) := by
    have hh := ha (Sum.inl ⟨i,j,l⟩)
    change (c i j).direction l=_ at hh
    rw [hh]
    exact wiener_finite_linearity P W.toLinearMap e _
  filter_upwards [ae_all_iff.mpr (fun j => ae_all_iff.mpr (hx j))] with w hw
  have hc (j:Fin (q i)) : (c i j).value P W w=(c i j).f (L i j (fun m => W (e m) w)) := by
    unfold SmoothCylinder.value
    congr 1
    funext l
    exact (hw j l).trans (cylinder_coordinate_map_apply
      (fun l:Fin (c i j).dim => a (Sum.inl ⟨i,j,l⟩)) (fun m => W (e m) w) l).symm
  simp_rw [hc]
  have hv (j:Fin (q i)) : v i j=∑m,a (Sum.inr ⟨i,j⟩) m • e m := ha (Sum.inr ⟨i,j⟩)
  simp_rw [hv,Finset.smul_sum,smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  rw [←Finset.sum_smul]
  congr 1
  change (∑j,(c i j).f (L i j (fun m => W (e m) w))*a (Sum.inr ⟨i,j⟩) l)=
    ∑j,a (Sum.inr ⟨i,j⟩) l*(c i j).f (L i j (fun m => W (e m) w))
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
end Asakura.Chapter12
#print axioms Asakura.Chapter12.vector_family_common_frame

import Chapter12GaussianCoreDivergence
import FullAuditCommonOrthonormal

open MeasureTheory ProbabilityTheory Set
namespace Asakura.Chapter12
open Asakura.FullAudit
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4500000

noncomputable def SmoothCylinder.coordinateJet {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] (c : SmoothCylinder H) : GaussianJet c.dim :=
  ⟨c.f,c.smooth,c.all_derivatives_growth⟩

noncomputable def GaussianJet.compLinear {n m : ℕ} (f : GaussianJet n)
    (L : (Fin m → ℝ) →L[ℝ] (Fin n → ℝ)) : GaussianJet m :=
  ⟨f.f ∘ L,f.smooth.comp L.contDiff,iterated_polynomial_growth_comp_linear f.f f.smooth L f.growth⟩

/-- Every finite vector cylinder can use one orthonormal frame containing
both its Wiener directions and its vector values. No restriction of the
original smooth core is introduced by the finite-dimensional estimate. -/
theorem finite_vector_cylinder_orthonormal_representation {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Nontrivial H]
    (P : Measure Ω) (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) {q : ℕ}
    (c : Fin q → SmoothCylinder H) (v : Fin q → H) :
    ∃ (n : ℕ) (e : Fin (n+1) → H) (u : Fin (n+1) → GaussianJet (n+1)),
      Orthonormal ℝ e ∧
      (fun w => ∑ j,(c j).value P W w • v j)=ᵐ[P]
        (fun w => ∑ i,(u i).f (fun j => W (e j) w) • e i) := by
  classical
  let dirs : ((Σ j : Fin q,Fin (c j).dim) ⊕ Fin q) → H :=
    Sum.elim (fun ji => (c ji.1).direction ji.2) v
  obtain ⟨n,e,a,he,ha⟩ := finite_common_orthonormal dirs
  let L := fun j => cylinderCoordinateMap (fun k : Fin (c j).dim => a (Sum.inl ⟨j,k⟩))
  let u := fun i => GaussianJet.finsetSum Finset.univ (fun j : Fin q =>
    (((c j).coordinateJet).compLinear (L j)).smul (a (Sum.inr j) i))
  refine ⟨n,e,u,he,?_⟩
  have hx (j : Fin q) (k : Fin (c j).dim) :
      (W ((c j).direction k) : Ω → ℝ)=ᵐ[P]
        (fun w => ∑ i,a (Sum.inl ⟨j,k⟩) i*W (e i) w) := by
    have hh := ha (Sum.inl ⟨j,k⟩)
    change (c j).direction k=_ at hh
    rw [hh]
    exact wiener_finite_linearity P W.toLinearMap e _
  filter_upwards [ae_all_iff.mpr (fun j => ae_all_iff.mpr (hx j))] with w hw
  have hc (j : Fin q) : (c j).value P W w=(c j).f (L j (fun i => W (e i) w)) := by
    unfold SmoothCylinder.value
    congr 1
    funext k
    exact (hw j k).trans (cylinder_coordinate_map_apply (fun k : Fin (c j).dim => a (Sum.inl ⟨j,k⟩)) (fun i => W (e i) w) k).symm
  simp_rw [hc]
  have hv (j : Fin q) : v j=∑ i,a (Sum.inr j) i • e i := ha (Sum.inr j)
  simp_rw [hv,Finset.smul_sum,smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_smul]
  congr 1
  change (∑ j,(c j).f (L j (fun i => W (e i) w))*a (Sum.inr j) i)=
    ∑ j,a (Sum.inr j) i*(c j).f (L j (fun i => W (e i) w))
  exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)

end Asakura.Chapter12

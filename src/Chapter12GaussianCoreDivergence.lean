import Chapter12GaussianTensorIndexOrder
import Chapter12CylinderDirectionDivergence

open MeasureTheory ProbabilityTheory Set ENNReal
open scoped RealInnerProductSpace
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4500000

variable {Ω : Type*} [MeasurableSpace Ω] (H : RealHilbertSpaceData) [Nontrivial H]
  (P : Measure Ω) [IsProbabilityMeasure P]
  (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
  (hcore : ∀ h∈S,HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)

theorem gaussian_tensor_core_zero {N : ℕ} (u : Fin N → GaussianJet N) (e : Fin N → H) :
    gaussianTensorCore H P W S hS hcore 2 (by simp) u e 0=
      ∑ i,vectorCylinderValue P W S hS hcore ((u i).toCylinder e) (e i) 2 (by simp) := by
  unfold gaussianTensorCore
  exact (Equiv.sum_comp (Equiv.funUnique (Fin 1) (Fin N))
    (fun i => vectorCylinderValue P W S hS hcore ((u i).toCylinder e) (e i) 2 (by simp)))

theorem gaussian_cylinder_ibp_coordinate {N : ℕ} (f : GaussianJet N)
    (e : Fin N → H) (he : Orthonormal ℝ e) (i : Fin N) (w : Ω) :
    (f.toCylinder e).ibpTest P W (e i) w=
      W (e i) w*f.f (fun j => W (e j) w)-(f.partial i).f (fun j => W (e j) w) := by
  classical
  unfold SmoothCylinder.ibpTest SmoothCylinder.gradient SmoothCylinder.value
  change f.f (fun j => W (e j) w)*W (e i) w-
    inner ℝ (∑ j,fderiv ℝ f.f (fun j => W (e j) w) (Pi.single j 1) • e j) (e i)=_
  rw [he.inner_left_fintype]
  simp only [starRingEnd_apply,star_trivial,GaussianJet.partial]
  ring

/-- The Gaussian divergence whose moments were estimated is exactly the
adjoint divergence of the book's closed Malliavin derivative. -/
theorem gaussian_core_is_divergence {N : ℕ} (u : Fin N → GaussianJet N)
    (e : Fin N → H) (he : Orthonormal ℝ e)
    (D : Lp ℝ 2 P →ₗ.[ℝ] Lp H 2 P)
    (hgraph : (D.graph : Set _) = closure (range (cylinderPair P W S hS hcore 2 (by simp)))) :
    IsDivergence D (gaussianTensorCore H P W S hS hcore 2 (by simp) u e 0)
      ((GaussianJet.divergence u).toCylinder e |>.valueLp P W S hS hcore 2 (by simp)) := by
  classical
  have hd (i : Fin N) : IsDivergence D
      (vectorCylinderValue P W S hS hcore ((u i).toCylinder e) (e i) 2 (by simp))
      (((u i).toCylinder e).ibpTestLp P W S hS hcore (e i) 2 (by simp)) := by
    obtain ⟨hi,hd⟩ := cylinder_direction_divergence P W S hS hcore D hgraph ((u i).toCylinder e) (e i)
    have heq : hi.toLp _=vectorCylinderValue P W S hS hcore ((u i).toCylinder e) (e i) 2 (by simp) := by
      apply Lp.ext
      exact hi.coeFn_toLp.trans (vector_cylinder_value_coe H P W S hS hcore 2 (by simp) _ _).symm
    rwa [heq] at hd
  have hz : ((GaussianJet.divergence u).toCylinder e).valueLp P W S hS hcore 2 (by simp)=
      ∑ i,((u i).toCylinder e).ibpTestLp P W S hS hcore (e i) 2 (by simp) := by
    apply Lp.ext
    filter_upwards [((GaussianJet.divergence u).toCylinder e |>.value_memLp P W S hS hcore 2 (by simp)).coeFn_toLp,
      Lp.coeFn_fun_finsetSum Finset.univ (fun i => ((u i).toCylinder e).ibpTestLp P W S hS hcore (e i) 2 (by simp)),
      ae_all_iff.mpr (fun i => (((u i).toCylinder e).ibpTest_memLp P W S hS hcore (e i) 2 (by simp)).coeFn_toLp)] with w hw hs hi
    change ((GaussianJet.divergence u).toCylinder e).valueLp P W S hS hcore 2 (by simp) w=_ at hw ⊢
    rw [hw,hs]
    change (GaussianJet.divergence u).f (fun i => W (e i) w)=_
    rw [GaussianJet.divergence_apply]
    apply Finset.sum_congr rfl
    intro i _
    exact (hi i).trans (gaussian_cylinder_ibp_coordinate H P W (u i) e he i w) |>.symm
  rw [gaussian_tensor_core_zero H P W S hS hcore,hz]
  intro f
  simp only [inner_sum]
  exact Finset.sum_congr rfl (fun i _ => hd i f)

end Asakura.Chapter12

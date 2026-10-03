import Chapter8QuadraticNewtonPaths
import Chapter8QuadraticDerivativeBounds

open Finset
open scoped BigOperators RealInnerProductSpace
namespace Asakura.Chapter8
attribute [local instance] scalarOpNormed scalarOpSpace scalarBiNormed scalarBiSpace
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

/-- Strict positivity of a finite-dimensional symmetric force supplies
uniform positive lower and upper Hessian bounds. -/
theorem positive_quadratic_bounds {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E]
    (K : E →L[ℝ] E) (hs : K.toLinearMap.IsSymmetric)
    (hK : ∀ z≠0,0<⟪z,K z⟫) :
    ∃ κ L : ℝ,0<κ ∧ κ≤L ∧ ∀ z,κ*‖z‖^2≤⟪z,K z⟫ ∧ ⟪z,K z⟫≤L*‖z‖^2 := by
  classical
  let B := hs.eigenvectorBasis rfl
  let ev := hs.eigenvalues rfl
  have he i : K (B i)=ev i • B i := hs.apply_eigenvectorBasis rfl i
  have hp i : 0<ev i := by
    have hh := hK (B i) (B.orthonormal.ne_zero i)
    rw [he,inner_smul_right,real_inner_self_eq_norm_sq,B.orthonormal.norm_eq_one] at hh
    simpa using hh
  haveI : Nonempty (Fin (Module.finrank ℝ E)) := Fin.pos_iff_nonempty.mp Module.finrank_pos
  let κ := univ.inf' univ_nonempty ev
  let L := univ.sup' univ_nonempty ev
  have hk : 0<κ := (lt_inf'_iff _).mpr (fun i _ => hp i)
  have hl i : κ≤ev i := inf'_le ev (mem_univ i)
  have hu i : ev i≤L := le_sup' ev (mem_univ i)
  have hform z : ⟪z,K z⟫=∑ i,ev i*⟪B i,z⟫^2 := by
    rw [←B.sum_inner_mul_inner z (K z)]
    apply sum_congr rfl
    intro i _
    have hh : ⟪B i,K z⟫=ev i*⟪B i,z⟫ := by
      have hh : ⟪K (B i),z⟫=⟪B i,K z⟫ := hs (B i) z
      rw [←hh,he,real_inner_smul_left]
    rw [hh,real_inner_comm z (B i)]
    ring
  refine ⟨κ,L,hk,(hl (Classical.choice inferInstance)).trans (hu _),?_⟩
  intro z
  rw [hform,←B.sum_sq_inner_right z,mul_sum,mul_sum]
  exact ⟨sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hl i) (sq_nonneg _)),
    sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hu i) (sq_nonneg _))⟩

/-- For the actual quadratic potential the gradient is Kx, the Hessian is
constant and the third derivative vanishes. -/
theorem quadratic_potential_derivatives {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (K : E →L[ℝ] E) (hs : K.toLinearMap.IsSymmetric) :
    let U := fun x => ⟪x,K x⟫/2
    ContDiff ℝ 3 U ∧
    (∀ x, fderiv ℝ U x=innerSL ℝ (K x)) ∧
    (∀ x z w,fderiv ℝ (fderiv ℝ U) x z w=⟪K z,w⟫) ∧
    (∀ x,fderiv ℝ (fderiv ℝ (fderiv ℝ U)) x=0) := by
  dsimp only
  let D := (innerSL ℝ).comp K
  have hD : (fun x => ⟪x,K x⟫/2)=fun x => ((1/2:ℝ) • D) x x := by
    funext x
    simp only [D,ContinuousLinearMap.smul_apply,ContinuousLinearMap.comp_apply,innerSL_apply_apply,smul_eq_mul]
    rw [real_inner_comm]
    ring
  have hsym : D.flip=D := by
    ext x y
    change ⟪K y,x⟫=⟪K x,y⟫
    have hx : ⟪K y,x⟫=⟪y,K x⟫ := hs y x
    exact hx.trans (real_inner_comm _ _)
  have h1 : fderiv ℝ (fun x => ⟪x,K x⟫/2)=D := by
    rw [hD,quadratic_fderiv]
    funext x
    apply ContinuousLinearMap.ext
    intro y
    simp only [D,ContinuousLinearMap.add_apply,ContinuousLinearMap.flip_apply,
      ContinuousLinearMap.smul_apply,ContinuousLinearMap.comp_apply,innerSL_apply_apply,smul_eq_mul]
    have hh : ⟪K y,x⟫=⟪K x,y⟫ := by
      have hx : ⟪K y,x⟫=⟪y,K x⟫ := hs y x
      exact hx.trans (real_inner_comm _ _)
    rw [hh]
    ring
  refine ⟨?_,?_,?_,?_⟩
  · rw [hD]
    exact ((1/2:ℝ) • D).contDiff.clm_apply contDiff_id
  · intro x
    rw [h1]
    rfl
  · intro x z w
    rw [h1,D.fderiv]
    rfl
  · intro x
    rw [h1]
    have h2 : fderiv ℝ (fun y => D y)=fun _ => D := by funext y; exact D.fderiv
    rw [h2]
    exact fderiv_const_apply _
end Asakura.Chapter8

import Chapter8PositiveQuadraticBounds
import Chapter8DiagonalCoordinates
import Chapter8AffineQuadraticDensity

open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace ENNReal
namespace Asakura.Chapter8
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

/-- The spectral square root provides the actual normal transformation
for the quadratic position Gibbs measure. -/
theorem quadratic_gaussian_factor {d : ℕ}
    (K : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (hs : K.toLinearMap.IsSymmetric) (hK : ∀ z≠0,0<⟪z,K z⟫)
    (β : ℝ) (hβ : 0<β) :
    let e := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm
    ∃ L : (Fin d → ℝ) ≃L[ℝ] (Fin d → ℝ),
      (∀ x,(∑ i,(L.symm x i)^2)=β*⟪e x,K (e x)⟫) ∧
      volume.withDensity (fun x : Fin d → ℝ => ENNReal.ofReal
        ((∫ y : Fin d → ℝ,Real.exp (-β*(⟪e y,K (e y)⟫/2)))⁻¹*Real.exp (-β*(⟪e x,K (e x)⟫/2))))=
        (Measure.pi (fun _ : Fin d => gaussianReal 0 1)).map L := by
  dsimp only
  let e := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm
  let B : OrthonormalBasis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)) := hs.eigenvectorBasis (by simp)
  let ev : Fin d → ℝ := hs.eigenvalues (by simp)
  have he (i : Fin d) : K (B i)=ev i • B i := hs.apply_eigenvectorBasis (by simp) i
  have hp i : 0<ev i := by
    have hh := hK (B i) (B.orthonormal.ne_zero i)
    rw [he,inner_smul_right,real_inner_self_eq_norm_sq,B.orthonormal.norm_eq_one] at hh
    simpa using hh
  let c := fun i => Real.sqrt (β*ev i)
  have hc i : c i≠0 := (Real.sqrt_pos.mpr (mul_pos hβ (hp i))).ne'
  let D := diagonalEuclideanEquiv c hc
  let A := e.trans (B.repr.toContinuousLinearEquiv.trans (D.trans e.symm))
  let L := A.symm
  have hform x : (∑ i,(L.symm x i)^2)=β*⟪e x,K (e x)⟫ := by
    have hcoord i : L.symm x i=c i*⟪B i,e x⟫ := by
      change c i*(B.repr (e x) i)=_
      rw [B.repr_apply_apply]
    have hf i : ⟪B i,K (e x)⟫=ev i*⟪B i,e x⟫ := by
      have hh : ⟪K (B i),e x⟫=⟪B i,K (e x)⟫ := hs (B i) (e x)
      rw [←hh,he,real_inner_smul_left]
    rw [←B.sum_inner_mul_inner (e x) (K (e x)),Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [hcoord,mul_pow,Real.sq_sqrt (mul_pos hβ (hp i)).le,hf,real_inner_comm (e x) (B i)]
    ring
  refine ⟨L,hform,?_⟩
  apply affine_quadratic_density L (fun x => ⟪e x,K (e x)⟫/2) (by fun_prop) β
  intro x
  rw [hform]
  ring
end Asakura.Chapter8

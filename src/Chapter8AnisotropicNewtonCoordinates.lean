import Chapter8DiagonalCoordinates
import Chapter8NewtonCoordinates

open scoped BigOperators RealInnerProductSpace
namespace Asakura.Chapter8
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

/-- Independent positive weights in the eigendirections, together with
the velocity shear, define one invertible quadratic coordinate system. -/
def anisotropicNewtonEquiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (C : E ≃L[ℝ] E) (δ : ℝ) : (E × E) ≃L[ℝ] WithLp 2 (E × E) :=
  let A : (E × E) ≃L[ℝ] (E × E) := {
    toFun := fun z => (C z.1,z.2+(δ/2) • z.1)
    invFun := fun z => (C.symm z.1,z.2-(δ/2) • C.symm z.1)
    left_inv := by intro z; simp
    right_inv := by intro z; simp
    map_add' := by intros; ext <;> simp [smul_add] <;> abel
    map_smul' := by
      intro a z
      change (C (a • z.1),a • z.2+(δ/2) • (a • z.1))=
        (a • C z.1,a • (z.2+(δ/2) • z.1))
      rw [map_smul]
      ext <;> module
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
  A.trans (WithLp.prodContinuousLinearEquiv 2 ℝ E E).symm

/-- The norm of these coordinates equals the sum of the scalar quadratic
energies used in the manuscript's eigendirection argument. -/
theorem anisotropic_newton_energy {d : ℕ} (b : Fin d → ℝ) (δ : ℝ)
    (hp : ∀ i,0<b i+δ^2/4) :
    let c := fun i => Real.sqrt (b i+δ^2/4)
    let C := diagonalEuclideanEquiv c (fun i => (Real.sqrt_pos.mpr (hp i)).ne')
    ∀ z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d),
      ‖anisotropicNewtonEquiv C δ z‖^2=∑ i,newtonEnergy δ (b i) (z.1 i) (z.2 i) := by
  dsimp only
  intro z
  rw [WithLp.prod_norm_sq_eq_of_L2]
  change ‖diagonalEuclideanEquiv _ _ z.1‖^2+‖z.2+(δ/2) • z.1‖^2=_
  rw [EuclideanSpace.real_norm_sq_eq,EuclideanSpace.real_norm_sq_eq,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  change (Real.sqrt (b i+δ^2/4)*z.1 i)^2+(z.2 i+(δ/2)*z.1 i)^2=_
  rw [mul_pow,Real.sq_sqrt (hp i).le]
  unfold newtonEnergy
  ring

end
end Asakura.Chapter8

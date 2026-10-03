import Chapter8NewtonNorm
import FullAuditTransportFlow

open MeasureTheory
namespace Asakura.Chapter8
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- An invertible linear coordinate change realizes the quadratic norm as an
ordinary Hilbert norm. It also preserves Borel measurability. -/
def newtonCoordinateEquiv (δ b : ℝ) (hp : 0 < b+δ^2/4) :
    (E × E) ≃L[ℝ] WithLp 2 (E × E) :=
  let c := Real.sqrt (b+δ^2/4)
  let A : (E × E) ≃L[ℝ] (E × E) := {
    toFun := fun z => (c • z.1,z.2+(δ/2) • z.1)
    invFun := fun z => (c⁻¹ • z.1,z.2-(δ/2) • (c⁻¹ • z.1))
    left_inv := by
      intro z
      have hc : c ≠ 0 := (Real.sqrt_pos.mpr hp).ne'
      simp [smul_smul,hc]
    right_inv := by
      intro z
      have hc : c ≠ 0 := (Real.sqrt_pos.mpr hp).ne'
      simp [smul_smul,hc]
    map_add' := by intros; ext <;> simp [smul_add] <;> abel
    map_smul' := by
      intro a z
      change (c • (a • z.1), a • z.2+(δ/2) • (a • z.1)) =
        (a • (c • z.1),a • (z.2+(δ/2) • z.1))
      ext <;> module
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
  A.trans (WithLp.prodContinuousLinearEquiv 2 ℝ E E).symm

theorem newton_coordinate_equiv_apply (δ b : ℝ) (hp : 0 < b+δ^2/4) (z : E × E) :
    newtonCoordinateEquiv δ b hp z = newtonCoordinates δ b z := rfl

/-- Taking square roots of the energy estimate gives precisely exp(-r t). -/
theorem newton_norm_contraction_of_energy (δ b r t : ℝ) (hp : 0 ≤ b+δ^2/4)
    (x y : E × E)
    (h : newtonVectorEnergy δ b x.1 x.2 ≤ Real.exp (-2*r*t)*newtonVectorEnergy δ b y.1 y.2) :
    newtonNorm δ b x ≤ Real.exp (-r*t)*newtonNorm δ b y := by
  have hs : (Real.exp (-r*t))^2 = Real.exp (-2*r*t) := by
    rw [pow_two,← Real.exp_add]
    congr 1; ring
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))).mp
  rw [mul_pow,hs]
  change (newtonNorm δ b x)^2 ≤ Real.exp (-2*r*t)*(newtonNorm δ b y)^2
  rw [newton_norm_square δ b hp,newton_norm_square δ b hp]
  exact h

end
end Asakura.Chapter8

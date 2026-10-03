import Chapter12AffineGaussianSmoothDensity

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

noncomputable def triangularGaussianEquiv (a b c : ℝ) (hb : b≠0) (hc : c≠0) :
    (Fin 2 → ℝ) ≃L[ℝ] (Fin 2 → ℝ) := {
  toFun := fun z => ![b*z 0,a*b*z 0+c*z 1]
  invFun := fun y => ![y 0/b,(y 1-a*y 0)/c]
  left_inv := by
    intro z
    funext i
    fin_cases i <;> dsimp <;> field_simp <;> ring
  right_inv := by
    intro z
    funext i
    fin_cases i <;> dsimp <;> field_simp <;> ring
  map_add' := by
    intro x y
    funext i
    fin_cases i <;> dsimp <;> ring
  map_smul' := by
    intro r x
    funext i
    fin_cases i <;> dsimp <;> ring
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop }

theorem two_direction_orthonormalization {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (h g : H) (a b c : ℝ) (hb : b≠0) (hc : c≠0)
    (hh : inner ℝ h h=b^2) (hg : inner ℝ h g=a*b^2)
    (hgg : inner ℝ g g=a^2*b^2+c^2) :
    Orthonormal ℝ (![b⁻¹ • h,c⁻¹ • (g-a • h)] : Fin 2 → H) := by
  have hgh : inner ℝ g h=a*b^2 := by rw [real_inner_comm]; exact hg
  rw [orthonormal_iff_ite]
  intro i j
  fin_cases i <;> fin_cases j
  · change inner ℝ (b⁻¹ • h) (b⁻¹ • h)=1
    rw [inner_smul_left,inner_smul_right,hh]
    simp only [RCLike.conj_to_real]
    field_simp
  · change inner ℝ (b⁻¹ • h) (c⁻¹ • (g-a • h))=0
    rw [inner_smul_left,inner_smul_right,inner_sub_right,inner_smul_right,hg,hh]
    simp only [RCLike.conj_to_real]
    ring
  · change inner ℝ (c⁻¹ • (g-a • h)) (b⁻¹ • h)=0
    rw [real_inner_comm,inner_smul_left,inner_smul_right,inner_sub_right,inner_smul_right,hg,hh]
    simp only [RCLike.conj_to_real]
    ring
  · change inner ℝ (c⁻¹ • (g-a • h)) (c⁻¹ • (g-a • h))=1
    simp only [inner_smul_left,inner_smul_right,inner_sub_left,inner_sub_right,hh,hg,hgh,hgg,
      RCLike.conj_to_real]
    field_simp
    <;> ring

end Asakura.Chapter12

import Chapter8LipschitzGrowthData

namespace Asakura.Chapter8
noncomputable def scalarCoordinate : (Fin 1 → ℝ) ≃L[ℝ] ℝ :=
  (show (Fin 1 → ℝ) ≃ₗ[ℝ] ℝ from
    { toFun := fun x => x 0
      invFun := fun r _ => r
      left_inv := fun x => by ext i; have hi : i=0 := Subsingleton.elim _ _; simp [hi]
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }).toContinuousLinearEquiv
@[simp] theorem scalarCoordinate_apply (x : Fin 1 → ℝ) : scalarCoordinate x=x 0 := rfl
@[simp] theorem scalarCoordinate_symm_apply (r : ℝ) : scalarCoordinate.symm r=(fun _ => r) := rfl
end Asakura.Chapter8

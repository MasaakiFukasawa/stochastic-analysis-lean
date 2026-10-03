import Chapter8PhaseCoordinates

namespace Asakura.Chapter8
noncomputable section

/-- The actual invertible coordinate map from a vector of phase coordinates
to its position and velocity in the spatial normed space. -/
def phaseLinearEquiv {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : (Fin d → ℝ) ≃L[ℝ] E) : (Fin (d+d) → ℝ) ≃L[ℝ] E × E where
  toFun z := (e (positionProjection d z),e (velocityProjection d z))
  invFun z := Fin.addCases (e.symm z.1) (e.symm z.2)
  left_inv z := by
    funext i
    refine Fin.addCases ?_ ?_ i <;> intro j <;>
      simp only [Fin.addCases_left,Fin.addCases_right,e.symm_apply_apply]
    <;> rfl
  right_inv z := by
    apply Prod.ext
    · change e (positionProjection d (Fin.addCases (e.symm z.1) (e.symm z.2)))=z.1
      have h : positionProjection d (Fin.addCases (e.symm z.1) (e.symm z.2))=e.symm z.1 := by
        ext i
        simp only [positionProjection,ContinuousLinearMap.pi_apply,ContinuousLinearMap.proj_apply,Fin.addCases_left]
      rw [h,e.apply_symm_apply]
    · change e (velocityProjection d (Fin.addCases (e.symm z.1) (e.symm z.2)))=z.2
      have h : velocityProjection d (Fin.addCases (e.symm z.1) (e.symm z.2))=e.symm z.2 := by
        ext i
        simp only [velocityProjection,ContinuousLinearMap.pi_apply,ContinuousLinearMap.proj_apply,Fin.addCases_right]
      rw [h,e.apply_symm_apply]
  map_add' z w := by simp only [map_add,Prod.mk_add_mk]
  map_smul' a z := by simp only [map_smul,Prod.smul_mk, RingHom.id_apply]
  continuous_toFun := (e.continuous.comp (positionProjection d).continuous).prodMk
    (e.continuous.comp (velocityProjection d).continuous)
  continuous_invFun := by
    apply continuous_pi
    intro i
    refine Fin.addCases ?_ ?_ i <;> intro j <;>
      simp only [Fin.addCases_left,Fin.addCases_right]
    · exact (continuous_apply j).comp (e.symm.continuous.comp continuous_fst)
    · exact (continuous_apply j).comp (e.symm.continuous.comp continuous_snd)

end
end Asakura.Chapter8

import Chapter8CosineHessianBounds

open scoped BigOperators
namespace Asakura.Chapter8
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

noncomputable def cosinePotential (d : ℕ) (k c : ℝ) (x : Fin d → ℝ) : ℝ :=
  ∑ i,(k*(x i)^2/2+c*(1-Real.cos (x i)))

/-- Coordinate differentiation verifies the Hessian used in the nonlinear
Newton example, directly from the displayed potential. -/
theorem cosine_potential_coordinate_derivative (d : ℕ) (k c : ℝ) :
    ContDiff ℝ 3 (cosinePotential d k c) ∧
    ∀ x i,fderiv ℝ (cosinePotential d k c) x (Pi.single i 1)=k*x i+c*Real.sin (x i) := by
  constructor
  · unfold cosinePotential
    fun_prop
  · intro x i
    let φ : ℝ → ℝ := fun y => k*y^2/2+c*(1-Real.cos y)
    have hd y : HasDerivAt φ (k*y+c*Real.sin y) y := by
      convert ((((hasDerivAt_id y).pow 2).const_mul k).div_const 2).add
        (((hasDerivAt_const y (1:ℝ)).sub (Real.hasDerivAt_cos y)).const_mul c) using 1
      · rfl
      · simp only [id_eq]; ring
    have hi j : HasFDerivAt (fun z : Fin d → ℝ => φ (z j))
        ((k*x j+c*Real.sin (x j)) • (ContinuousLinearMap.proj j : (Fin d → ℝ) →L[ℝ] ℝ)) x := by
      simpa only [Function.comp_def,ContinuousLinearMap.proj_apply,ContinuousLinearMap.smul_comp,ContinuousLinearMap.one_apply,
        ContinuousLinearMap.id_comp] using
        (hd (x j)).comp_hasFDerivAt x ((ContinuousLinearMap.proj j : (Fin d → ℝ) →L[ℝ] ℝ)).hasFDerivAt
    have hs := HasFDerivAt.sum (u := Finset.univ) (fun j _ => hi j)
    have hs' : HasFDerivAt (cosinePotential d k c)
      (∑ j,(k*x j+c*Real.sin (x j)) • (ContinuousLinearMap.proj j : (Fin d → ℝ) →L[ℝ] ℝ)) x := by
      convert hs using 1
      funext z
      simp [cosinePotential,φ]
    rw [hs'.fderiv]
    simp [Pi.single_apply]

 theorem cosine_gradient_derivative (d : ℕ) (k c : ℝ) (x : Fin d → ℝ) :
    HasFDerivAt (fun z : Fin d → ℝ => fun i => k*z i+c*Real.sin (z i))
      (ContinuousLinearMap.pi (fun i => (k+c*Real.cos (x i)) • (ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ))) x := by
  apply hasFDerivAt_pi.mpr
  intro i
  have hd : HasDerivAt (fun y : ℝ => k*y+c*Real.sin y) (k+c*Real.cos (x i)) (x i) := by
    convert ((hasDerivAt_id (x i)).const_mul k).add ((Real.hasDerivAt_sin (x i)).const_mul c) using 1
    · rfl
    · simp
  simpa only [Function.comp_def,ContinuousLinearMap.proj_apply,ContinuousLinearMap.smul_comp,ContinuousLinearMap.one_apply,
    ContinuousLinearMap.id_comp] using
    hd.comp_hasFDerivAt x ((ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ)).hasFDerivAt

end Asakura.Chapter8

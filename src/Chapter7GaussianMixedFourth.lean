import Chapter7GaussianFourthLaw

open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace Asakura.Chapter7
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

/-- Mixed fourth moments follow by polarization from the actual Gaussian laws
of linear combinations. Repeated coordinates and singular covariance are allowed. -/
theorem gaussian_mixed_fourth
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Fin 4 → Ω → ℝ) (a : Fin 4 → Fin 4 → ℝ)
    (v : ℝ → ℝ → ℝ → ℝ≥0)
    (h : ∀ s t u, HasLaw (fun w => X 0 w+s*X 1 w+t*X 2 w+u*X 3 w)
      (gaussianReal 0 (v s t u)) P)
    (hv : ∀ s t u,(v s t u : ℝ) = a 0 0+s^2*a 1 1+t^2*a 2 2+u^2*a 3 3+2*(s*a 0 1+t*a 0 2+u*a 0 3+s*t*a 1 2+s*u*a 1 3+t*u*a 2 3)) :
    Integrable (fun w => X 0 w*X 1 w*X 2 w*X 3 w) P ∧
    (∫ w,X 0 w*X 1 w*X 2 w*X 3 w ∂P) =
      a 0 1*a 2 3+a 0 2*a 1 3+a 0 3*a 1 2 := by
  let V0 := fun w => (X 0 w+(1:ℝ)*X 1 w+(1:ℝ)*X 2 w+(1:ℝ)*X 3 w)^4
  have h0 : Integrable V0 P ∧ (∫ w,V0 w ∂P)=3*(v (1) (1) (1):ℝ)^2 :=
    gaussian_fourth_law P _ _ (h (1) (1) (1))
  let V1 := fun w => (X 0 w+(1:ℝ)*X 1 w+(1:ℝ)*X 2 w+(-1:ℝ)*X 3 w)^4
  have h1 : Integrable V1 P ∧ (∫ w,V1 w ∂P)=3*(v (1) (1) (-1):ℝ)^2 :=
    gaussian_fourth_law P _ _ (h (1) (1) (-1))
  let V2 := fun w => (X 0 w+(1:ℝ)*X 1 w+(-1:ℝ)*X 2 w+(1:ℝ)*X 3 w)^4
  have h2 : Integrable V2 P ∧ (∫ w,V2 w ∂P)=3*(v (1) (-1) (1):ℝ)^2 :=
    gaussian_fourth_law P _ _ (h (1) (-1) (1))
  let V3 := fun w => (X 0 w+(1:ℝ)*X 1 w+(-1:ℝ)*X 2 w+(-1:ℝ)*X 3 w)^4
  have h3 : Integrable V3 P ∧ (∫ w,V3 w ∂P)=3*(v (1) (-1) (-1):ℝ)^2 :=
    gaussian_fourth_law P _ _ (h (1) (-1) (-1))
  let V4 := fun w => (X 0 w+(-1:ℝ)*X 1 w+(1:ℝ)*X 2 w+(1:ℝ)*X 3 w)^4
  have h4 : Integrable V4 P ∧ (∫ w,V4 w ∂P)=3*(v (-1) (1) (1):ℝ)^2 :=
    gaussian_fourth_law P _ _ (h (-1) (1) (1))
  let V5 := fun w => (X 0 w+(-1:ℝ)*X 1 w+(1:ℝ)*X 2 w+(-1:ℝ)*X 3 w)^4
  have h5 : Integrable V5 P ∧ (∫ w,V5 w ∂P)=3*(v (-1) (1) (-1):ℝ)^2 :=
    gaussian_fourth_law P _ _ (h (-1) (1) (-1))
  let V6 := fun w => (X 0 w+(-1:ℝ)*X 1 w+(-1:ℝ)*X 2 w+(1:ℝ)*X 3 w)^4
  have h6 : Integrable V6 P ∧ (∫ w,V6 w ∂P)=3*(v (-1) (-1) (1):ℝ)^2 :=
    gaussian_fourth_law P _ _ (h (-1) (-1) (1))
  let V7 := fun w => (X 0 w+(-1:ℝ)*X 1 w+(-1:ℝ)*X 2 w+(-1:ℝ)*X 3 w)^4
  have h7 : Integrable V7 P ∧ (∫ w,V7 w ∂P)=3*(v (-1) (-1) (-1):ℝ)^2 :=
    gaussian_fourth_law P _ _ (h (-1) (-1) (-1))
  let R := fun w => V0 w-V1 w-V2 w+V3 w-V4 w+V5 w+V6 w-V7 w
  have hi : Integrable R P := ((((((h0.1.sub h1.1).sub h2.1).add h3.1).sub h4.1).add h5.1).add h6.1).sub h7.1
  have he w : R w=192*(X 0 w*X 1 w*X 2 w*X 3 w) := by dsimp [R,V0,V1,V2,V3,V4,V5,V6,V7]; ring
  have hp : Integrable (fun w => X 0 w*X 1 w*X 2 w*X 3 w) P := by
    apply (hi.const_mul (1/192:ℝ)).congr
    filter_upwards [] with w
    rw [he]; ring
  refine ⟨hp,?_⟩
  have heint : (∫ w,R w ∂P)=192*(∫ w,X 0 w*X 1 w*X 2 w*X 3 w ∂P) := by
    simp_rw [he]; exact integral_const_mul _ _
  have hr : (∫ w,R w ∂P) = 192*(a 0 1*a 2 3+a 0 2*a 1 3+a 0 3*a 1 2) := by
    dsimp only [R]
    have i1 : Integrable (fun w => V0 w-V1 w) P := h0.1.sub h1.1
    have i2 : Integrable (fun w => V0 w-V1 w-V2 w) P := i1.sub h2.1
    have i3 : Integrable (fun w => V0 w-V1 w-V2 w+V3 w) P := i2.add h3.1
    have i4 : Integrable (fun w => V0 w-V1 w-V2 w+V3 w-V4 w) P := i3.sub h4.1
    have i5 : Integrable (fun w => V0 w-V1 w-V2 w+V3 w-V4 w+V5 w) P := i4.add h5.1
    have i6 : Integrable (fun w => V0 w-V1 w-V2 w+V3 w-V4 w+V5 w+V6 w) P := i5.add h6.1
    have i7 : Integrable (fun w => V0 w-V1 w-V2 w+V3 w-V4 w+V5 w+V6 w-V7 w) P := i6.sub h7.1
    rw [integral_sub i6 h7.1,
      integral_add i5 h6.1,
      integral_add i4 h5.1,
      integral_sub i3 h4.1,
      integral_add i2 h3.1,
      integral_sub i1 h2.1,
      integral_sub h0.1 h1.1,
      h0.2,h1.2,h2.2,h3.2,h4.2,h5.2,h6.2,h7.2]
    simp only [hv]
    ring
  linarith

end Asakura.Chapter7

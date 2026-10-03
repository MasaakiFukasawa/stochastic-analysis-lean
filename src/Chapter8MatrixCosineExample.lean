import Chapter8CosineBoundedDerivatives
import Chapter8QuadraticDerivativeBounds

open scoped BigOperators NNReal
namespace Asakura.Chapter8
attribute [local instance] scalarOpNormed scalarOpSpace scalarBiNormed scalarBiSpace
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

/-- The example with a general symmetric matrix A satisfies strong
monotonicity with the lower eigenvalue bound diminished by |c|. -/
theorem matrix_cosine_strong_monotonicity {d : ℕ}
    (A : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) (a c : ℝ)
    (hA : ∀ z,a*(∑ i,z i^2)≤∑ i,z i*A z i) (x y : Fin d → ℝ) :
    (a-|c|)*(∑ i,(x i-y i)^2)≤
      ∑ i,(x i-y i)*((A x i+c*Real.sin (x i))-(A y i+c*Real.sin (y i))) := by
  have hlin := hA (x-y)
  simp only [map_sub,Pi.sub_apply] at hlin
  have hcos := cosine_gradient_strong_monotonicity (d := d) 0 c x y
  simp only [zero_mul,zero_add,zero_sub] at hcos
  calc
    _ = a*(∑ i,(x i-y i)^2)+(-|c|)*(∑ i,(x i-y i)^2) := by ring
    _ ≤ (∑ i,(x i-y i)*(A x i-A y i))+
        ∑ i,(x i-y i)*(c*Real.sin (x i)-c*Real.sin (y i)) := add_le_add hlin hcos
    _ = _ := by rw [←Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro i _; ring

/-- Differentiate the displayed matrix-quadratic plus cosine potential;
the linear part of its gradient is the actual matrix A. -/
theorem matrix_cosine_potential_derivative {d : ℕ}
    (A : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) (c : ℝ)
    (hA : ∀ x y,(∑ i,x i*A y i)=∑ i,y i*A x i) :
    ∀ x i,fderiv ℝ (fun z => (∑ j,z j*A z j)/2+cosinePotential d 0 c z) x
      (Pi.single i 1)=A x i+c*Real.sin (x i) := by
  let B : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) →L[ℝ] ℝ :=
    ∑ i,(ContinuousLinearMap.proj i).smulRight ((ContinuousLinearMap.proj i).comp A)
  have he x y : B x y=∑ i,x i*A y i := by
    simp [B,ContinuousLinearMap.sum_apply]
  have hq : (fun z => (∑ j,z j*A z j)/2)=fun z => ((1/2:ℝ) • B) z z := by
    funext z
    simp only [ContinuousLinearMap.smul_apply,smul_eq_mul,he]
    ring
  have hc := (cosine_potential_coordinate_derivative d 0 c).1
  have hqd : Differentiable ℝ (fun z => (∑ j,z j*A z j)/2) := by
    rw [hq]
    have hh : ContDiff ℝ 3 (fun z => ((1/2:ℝ) • B) z z) := ((1/2:ℝ) • B).contDiff.clm_apply contDiff_id
    exact hh.differentiable (by norm_num)
  intro x i
  change (fderiv ℝ ((fun z => (∑ j,z j*A z j)/2)+cosinePotential d 0 c) x) _=_
  rw [fderiv_add (hqd x) ((hc.differentiable (by norm_num)) x),ContinuousLinearMap.add_apply]
  rw [cosine_potential_coordinate_derivative d 0 c |>.2]
  simp only [zero_mul,zero_add]
  rw [hq,quadratic_fderiv]
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.flip_apply,smul_eq_mul,he]
  rw [hA x (Pi.single i 1)]
  simp [Pi.single_apply]
  <;> ring

/-- The general matrix example also satisfies the global regularity
hypotheses: adding a quadratic form does not change the third derivative. -/
theorem matrix_cosine_potential_regularity {d : ℕ}
    (A : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) (c : ℝ) :
    let U := fun z => (∑ j,z j*A z j)/2+cosinePotential d 0 c z
    ContDiff ℝ 3 U ∧ ∃ C₂ C₃ : ℝ≥0,
      (∀ x,‖fderiv ℝ (fderiv ℝ U) x‖≤(C₂:ℝ)) ∧
      (∀ x,‖fderiv ℝ (fderiv ℝ (fderiv ℝ U)) x‖≤(C₃:ℝ)) := by
  let B : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) →L[ℝ] ℝ :=
    (1/2:ℝ) • ∑ i,(ContinuousLinearMap.proj i).smulRight ((ContinuousLinearMap.proj i).comp A)
  obtain ⟨A₂,A₃,h₂,h₃⟩ := cosine_potential_bounded_derivatives d 0 c
  have hh := add_quadratic_derivative_bounds (cosinePotential d 0 c)
    (cosine_potential_coordinate_derivative d 0 c).1 B A₂ A₃ h₂ h₃
  have he : (fun x => cosinePotential d 0 c x+B x x)=
      fun z => (∑ j,z j*A z j)/2+cosinePotential d 0 c z := by
    funext z
    simp [B]
    <;> ring
  rw [he] at hh
  exact hh

end Asakura.Chapter8

import Chapter9EuclideanDensityPDE
import Chapter9DensityScoreDerivatives
import Chapter9ProbabilityFlowExistence

open MeasureTheory Set
open scoped RealInnerProductSpace ContDiff
namespace Asakura.Chapter9
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

 theorem trace_continuity_algebra {d : ℕ} (p : ℝ) (hp : p≠0)
    (g y : EuclideanSpace ℝ (Fin d))
    (H : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :
    euclideanTrace d H+(d:ℝ)*p+⟪y,g⟫+⟪g,-y-p⁻¹ • g⟫=
      -p*euclideanTrace d (-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d))-
        (p⁻¹ • H-dyad (p⁻¹ • g) (p⁻¹ • g))) := by
  have hdyad : dyad (p⁻¹ • g) (p⁻¹ • g)=(p⁻¹*p⁻¹) • dyad g g := by
    simp only [map_smul,smul_apply,smul_smul]
  rw [hdyad]
  simp only [map_sub,map_neg,map_smul,euclidean_trace_identity,euclidean_trace_dyad,
    inner_sub_right,inner_neg_right,real_inner_smul_right,real_inner_smul_left,smul_eq_mul]
  rw [real_inner_comm g y]
  field_simp
  <;> ring

/-- The exact Gaussian-mixture density and the exact probability-flow
velocity satisfy the continuity equation, expressed with actual joint and
spatial Fréchet derivatives. -/
theorem ou_probability_continuity_equation {d : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (R : ℝ) (hb : ∀ᵐ x ∂μ,‖x‖≤R) (t : ℝ) (ht : 0<t)
    (y : EuclideanSpace ℝ (Fin d)) :
    (fderiv ℝ (ouEuclideanDensity μ) (t,y)) (1,ouProbabilityVelocity μ d t y)=
      -ouEuclideanDensity μ (t,y)*
        euclideanTrace d (fderiv ℝ (ouProbabilityVelocity μ d t) y) := by
  let a := Real.exp (-t)
  let v := 1-Real.exp (-2*t)
  let c := Real.exp (-(d:ℝ)/2*Real.log (2*Real.pi*v))
  let p := fun z => ∫ x,radialKernel c a v x z ∂μ
  let g := fun z => ∫ x,(-radialKernel c a v x z/v) • (z-a • x) ∂μ
  let H := ∫ x,(-radialKernel c a v x y/v) • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d))+
    ((radialKernel c a v x y/v^2) • innerSL ℝ (y-a • x)).smulRight (y-a • x) ∂μ
  have hv : 0<v := ou_variance_positive t ht
  have hp : 0<p y := radial_mixture_positive μ c a v (Real.exp_pos _) hv y
  obtain ⟨hpg,hsg⟩ := radial_density_score_derivatives μ c a v (Real.exp_pos _) hv y
  have he : (fun z => ouEuclideanDensity μ (t,z))=p := by
    funext z
    exact euclidean_density_radial μ t z
  have hV : HasFDerivAt (ouProbabilityVelocity μ d t)
      (-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d))-
        ((p y)⁻¹ • H-dyad ((p y)⁻¹ • g y) ((p y)⁻¹ • g y))) y :=
    (hasFDerivAt_id y).neg.sub hsg
  have hP := ((ou_euclidean_density_smooth μ).contDiffAt
    ((isOpen_lt continuous_const continuous_fst).mem_nhds (show 0<(t,y).1 from ht))).differentiableAt (by simp)
  have htime := hP.hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t y))
  have htime' := euclidean_density_time_pde μ R hb t ht y
  have htimeval : (fderiv ℝ (ouEuclideanDensity μ) (t,y)) (1,0)=
      euclideanTrace d H+(d:ℝ)*p y+⟪y,g y⟫ := by
    have hd : HasDerivAt (fun s => ouEuclideanDensity μ (s,y))
        ((fderiv ℝ (ouEuclideanDensity μ) (t,y)) (1,0)) t := by
      simpa only [Function.comp_def,id_eq] using! htime
    have hh := hd.unique htime'
    simpa only [euclidean_density_radial] using hh
  have hspace := hP.hasFDerivAt.comp y ((hasFDerivAt_const t y).prodMk (hasFDerivAt_id y))
  have hspace' : HasFDerivAt p
      ((fderiv ℝ (ouEuclideanDensity μ) (t,y)).comp
        ((0 : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ _))) y := by
    simpa only [Function.comp_def,id_eq,he] using! hspace
  have hspaceval (h : EuclideanSpace ℝ (Fin d)) :
      (fderiv ℝ (ouEuclideanDensity μ) (t,y)) (0,h)=⟪g y,h⟫ := by
    have hh := congrArg (fun L : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ => L h) (hspace'.unique hpg)
    simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.prod_apply,zero_apply,
      ContinuousLinearMap.id_apply,innerSL_apply_apply] using hh
  rw [show ((1:ℝ),ouProbabilityVelocity μ d t y)=(1,0)+(0,ouProbabilityVelocity μ d t y) by simp,
    map_add,htimeval,hspaceval,hV.fderiv]
  change euclideanTrace d H+(d:ℝ)*p y+⟪y,g y⟫+⟪g y,-y-(p y)⁻¹ • g y⟫=
    -ouEuclideanDensity μ (t,y)*_
  rw [euclidean_density_radial]
  exact trace_continuity_algebra (p y) hp.ne' (g y) y H
end Asakura.Chapter9

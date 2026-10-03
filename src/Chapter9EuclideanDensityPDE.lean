import Chapter9EuclideanTimeDerivative
import Chapter9EuclideanTrace
import Chapter9CompactPriorIntegrable

open MeasureTheory Set
open scoped RealInnerProductSpace
namespace Asakura.Chapter9
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

 theorem gaussian_radial_pde_algebra {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a v k d : ℝ) (hv : v≠0) (hav : a^2+v=1) (x y : E) :
    (a^2*(‖y-a • x‖^2/v^2-d/v)-a*⟪x,y-a • x⟫/v)*k=
      (-k/v)*d+(k/v^2)*‖y-a • x‖^2+d*k+⟪y,(-k/v) • (y-a • x)⟫ := by
  have hi : ⟪y,y-a • x⟫=‖y-a • x‖^2+a*⟪x,y-a • x⟫ := by
    have hh := real_inner_self_eq_norm_sq (y-a • x)
    rw [inner_sub_left,real_inner_smul_left] at hh
    linarith
  rw [real_inner_smul_right,hi]
  rw [show a^2=1-v by linarith]
  field_simp
  <;> ring

/-- The Euclidean time derivative equals trace of the actual density Hessian
plus div(x p). All terms are integrated against the same initial measure. -/
theorem euclidean_density_time_pde {d : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (R : ℝ) (hb : ∀ᵐ x ∂μ,‖x‖≤R) (t : ℝ) (ht : 0<t)
    (y : EuclideanSpace ℝ (Fin d)) :
    let a := Real.exp (-t)
    let v := 1-Real.exp (-2*t)
    let c := Real.exp (-(d:ℝ)/2*Real.log (2*Real.pi*v))
    let k := fun x => radialKernel c a v x y
    let g := ∫ x,(-k x/v) • (y-a • x) ∂μ
    let H := ∫ x,(-k x/v) • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d))+
      ((k x/v^2) • innerSL ℝ (y-a • x)).smulRight (y-a • x) ∂μ
    HasDerivAt (fun s => ouEuclideanDensity μ (s,y))
      (euclideanTrace d H+(d:ℝ)*ouEuclideanDensity μ (t,y)+⟪y,g⟫) t := by
  let a := Real.exp (-t)
  let v := 1-Real.exp (-2*t)
  let c := Real.exp (-(d:ℝ)/2*Real.log (2*Real.pi*v))
  let k := fun x : EuclideanSpace ℝ (Fin d) => radialKernel c a v x y
  let G := fun x => (-k x/v) • (y-a • x)
  let H := fun x => (-k x/v) • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d))+
    ((k x/v^2) • innerSL ℝ (y-a • x)).smulRight (y-a • x)
  have hb' : ∀ᵐ x ∂μ,x∈Metric.closedBall (0:EuclideanSpace ℝ (Fin d)) R := by
    simpa only [Metric.mem_closedBall,dist_zero_right] using hb
  have hk : Integrable k μ := compact_prior_integrable μ _ (isCompact_closedBall 0 R) hb' k
    (by dsimp [k,radialKernel]; fun_prop)
  have hG : Integrable G μ := compact_prior_integrable μ _ (isCompact_closedBall 0 R) hb' G
    (by dsimp [G,k,radialKernel]; fun_prop)
  have hH : Integrable H μ := compact_prior_integrable μ _ (isCompact_closedBall 0 R) hb' H
    (by dsimp [H,k,radialKernel]; fun_prop)
  have htr x : euclideanTrace d (H x)=(-k x/v)*(d:ℝ)+(k x/v^2)*‖y-a • x‖^2 := by
    have he : ((k x/v^2) • innerSL ℝ (y-a • x)).smulRight (y-a • x)=
        (k x/v^2) • dyad (y-a • x) (y-a • x) := by
      ext h
      simp only [dyad_apply,ContinuousLinearMap.smulRight_apply,smul_apply,smul_smul,smul_eq_mul]
    simp only [H,he,map_add,map_smul,euclidean_trace_identity,euclidean_trace_dyad,
      real_inner_self_eq_norm_sq,smul_eq_mul]
  have hav : a^2+v=1 := by
    dsimp [a,v]
    rw [pow_two,←Real.exp_add,show -t + -t= -2*t by ring]
    ring
  have he x := gaussian_radial_pde_algebra a v (k x) (d:ℝ)
    (ou_variance_positive t ht).ne' hav x y
  have he' x : (a^2*(‖y-a • x‖^2/v^2-(d:ℝ)/v)-a*⟪x,y-a • x⟫/v)*k x=
      euclideanTrace d (H x)+(d:ℝ)*k x+⟪y,G x⟫ := by rw [htr]; exact he x
  have hti := (euclideanTrace d).integrable_comp hH
  have hgi := (innerSL ℝ y).integrable_comp hG
  have hd := euclidean_density_time_derivative μ t ht y
  change HasDerivAt _ (∫ x,(a^2*(‖y-a • x‖^2/v^2-(d:ℝ)/v)-a*⟪x,y-a • x⟫/v)*k x ∂μ) t at hd
  simp_rw [he'] at hd
  have hs := integral_add (hti.add (hk.const_mul (d:ℝ))) hgi
  dsimp only [Pi.add_apply] at hs
  simp only [innerSL_apply_apply] at hs
  have hgint := (innerSL ℝ y).integral_comp_comm hG
  simp only [innerSL_apply_apply] at hgint
  rw [hs,integral_add hti (hk.const_mul (d:ℝ)),integral_const_mul,
    (euclideanTrace d).integral_comp_comm hH,hgint] at hd
  simpa only [euclidean_density_radial] using hd
end Asakura.Chapter9

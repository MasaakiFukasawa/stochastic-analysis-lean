import Chapter9CenteredBilinear
import Chapter9ScoreDerivative

open MeasureTheory
open scoped RealInnerProductSpace
namespace Asakura.Chapter9
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false

theorem quotient_rank_one {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (p : ℝ) (g : E) :
    ((-((p)^2)⁻¹) • innerSL ℝ g).smulRight g= -dyad (p⁻¹ • g) (p⁻¹ • g) := by
  ext h
  simp only [dyad_apply,ContinuousLinearMap.smulRight_apply,smul_apply,map_smul,
    neg_apply,smul_smul,inv_pow,pow_two]
  module

/-- The derivative of the actual score is the identity term plus the
covariance operator of the actual normalized posterior. No Hessian formula
or posterior moment identity is assumed. -/
theorem radial_score_posterior_hessian {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (μ : Measure E) [IsProbabilityMeasure μ]
    (c a v : ℝ) (hc : 0<c) (hv : 0<v) (R : ℝ) (hR : 0≤R)
    (hb : ∀ᵐ x ∂μ,‖x‖≤R) (y : E) :
    let p := fun z => ∫ x,radialKernel c a v x z ∂μ
    let P := μ.withDensity (fun x => ENNReal.ofReal (radialKernel c a v x y/p y))
    HasFDerivAt (fun z => (p z)⁻¹ • (∫ x,(-radialKernel c a v x z/v) • (z-a • x) ∂μ))
      ((-1/v) • ContinuousLinearMap.id ℝ E+(a^2/v^2) • covarianceOperator P) y := by
  let k := fun x => radialKernel c a v x y
  let p := fun z => ∫ x,radialKernel c a v x z ∂μ
  let P := μ.withDensity (fun x => ENNReal.ofReal (k x/p y))
  haveI : IsProbabilityMeasure P := (radial_mixture_score μ c a v hc hv y).1
  have hp : 0<p y := radial_mixture_positive μ c a v hc hv y
  have hk : Measurable k := by dsimp [k,radialKernel]; fun_prop
  have hkpos x : 0≤k x := mul_nonneg hc.le (Real.exp_pos _).le
  have hbP : ∀ᵐ x ∂P,‖x‖≤R := normalized_density_preserves_ae μ k (p y) {x | ‖x‖≤R} hb
  have h2 : MemLp (fun x : E => x) 2 P :=
    (memLp_const (μ := P) (p := 2) R).of_le (by fun_prop) (by
      filter_upwards [hbP] with x hx
      simpa only [Real.norm_eq_abs,abs_of_nonneg hR] using hx)
  let z := fun x => y-a • x
  let m := y-a • (∫ x,x ∂P)
  let g := ∫ x,(-k x/v) • z x ∂μ
  let D := ∫ x,(-k x/v) • innerSL ℝ (z x) ∂μ
  let A := fun x => (-1/v) • ContinuousLinearMap.id ℝ E+(1/v^2) • dyad (z x) (z x)
  have hZ : MemLp z 2 P := (memLp_const y).sub (h2.const_smul a)
  have hZZ : Integrable (fun x => dyad (z x) (z x)) P :=
    bilinear_square_integrable P z hZ (dyad (E := E))
  have hA : (∫ x,A x ∂P)=(-1/v) • ContinuousLinearMap.id ℝ E+
      (1/v^2) • (∫ x,dyad (z x) (z x) ∂P) := by
    have hi : Integrable (fun x => (1/v^2) • dyad (z x) (z x)) P := hZZ.smul (1/v^2 : ℝ)
    rw [integral_add (integrable_const _) hi,integral_smul]
    simp only [integral_smul]
    simp
  have hw x : k x • A x=(-k x/v) • ContinuousLinearMap.id ℝ E+
      ((k x/v^2) • innerSL ℝ (z x)).smulRight (z x) := by
    ext h
    simp only [A,dyad_apply,smul_add,smul_apply,add_apply,
      ContinuousLinearMap.id_apply,ContinuousLinearMap.smulRight_apply,smul_smul]
    module
  have hH := normalized_density_integral μ k hk hkpos (p y) hp A
  rw [hA] at hH
  simp_rw [hw] at hH
  have hgp : (p y)⁻¹ • g=(-1/v) • m := by
    have hn := normalized_density_integral μ k hk hkpos (p y) hp (fun x => (-1/v) • z x)
    have he x : k x • ((-1/v) • z x)=(-k x/v) • z x := by
      rw [smul_smul]; congr 1; ring
    simp_rw [he] at hn
    exact hn.symm.trans (posterior_score_growth P a v R hv hR hbP y).1
  obtain ⟨B,hB,hbound⟩ := radial_kernel_derivative_bound (E := E) c a v hc.le hv
  have hgi : Integrable (fun x => (-k x/v) • z x) μ := by
    apply (integrable_const B).mono' (by dsimp [k,z,radialKernel]; fun_prop)
    apply ae_of_all
    intro x
    simpa only [norm_smul,innerSL_apply_norm] using hbound x y
  have hD : D=innerSL ℝ g := by
    have hh := (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ).integral_comp_comm hgi
    simpa only [map_smul] using hh
  have hsq : dyad ((p y)⁻¹ • g) ((p y)⁻¹ • g)=(1/v^2) • dyad m m := by
    rw [hgp]
    simp only [map_smul,smul_apply,smul_smul]
    congr 1
    ring
  have hcov : (∫ x,dyad (z x) (z x) ∂P)-dyad m m=a^2 • covarianceOperator P :=
    affine_dyad_covariance P h2 y a
  have hd := radial_score_fderiv μ c a v hc hv y
  apply hd.congr_fderiv
  change (p y)⁻¹ • (∫ x,(-k x/v) • ContinuousLinearMap.id ℝ E+
      ((k x/v^2) • innerSL ℝ (z x)).smulRight (z x) ∂μ)+
      ((-((p y)^2)⁻¹) • D).smulRight g=_
  rw [←hH,hD,quotient_rank_one,hsq]
  calc
    _ = (-1/v) • ContinuousLinearMap.id ℝ E+
        (1/v^2) • ((∫ x,dyad (z x) (z x) ∂P)-dyad m m) := by module
    _ = _ := by rw [hcov,smul_smul]; congr 1; congr 1; ring
end Asakura.Chapter9

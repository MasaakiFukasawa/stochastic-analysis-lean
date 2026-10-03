import Chapter9RadialKernelDerivative
import Chapter9PosteriorMeasure

open MeasureTheory Set
open scoped RealInnerProductSpace ENNReal
namespace Asakura.Chapter9
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- The logarithmic derivative of the actual mixture is the posterior
average of the component score. The numerator's integrability is obtained
from Gaussian decay, even for a prior without moments. -/
theorem radial_mixture_score {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]
    (μ : Measure E) [IsProbabilityMeasure μ] (c a v : ℝ) (hc : 0<c) (hv : 0<v) (y : E) :
    let p := fun z => ∫ x,radialKernel c a v x z ∂μ
    let posterior := μ.withDensity (fun x => ENNReal.ofReal (radialKernel c a v x y/p y))
    IsProbabilityMeasure posterior ∧
      HasFDerivAt (fun z => Real.log (p z))
        (innerSL ℝ (∫ x,(-1/v) • (y-a • x) ∂posterior)) y := by
  let k := fun x => radialKernel c a v x y
  let p := fun z => ∫ x,radialKernel c a v x z ∂μ
  have hm : Measurable k := by dsimp [k,radialKernel]; fun_prop
  have hpos x : 0<k x := mul_pos hc (Real.exp_pos _)
  have hi : Integrable k μ := by
    apply (integrable_const c).mono' hm.aestronglyMeasurable
    apply ae_of_all
    intro x
    rw [Real.norm_eq_abs,abs_of_pos (hpos x)]
    exact mul_le_of_le_one_right hc.le (Real.exp_le_one_iff.mpr
      (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by positivity)))
  have hp : 0<p y := by
    apply (integral_pos_iff_support_of_nonneg (fun x => (hpos x).le) hi).mpr
    have he : Function.support k=univ := by ext x; simp [Function.mem_support,(hpos x).ne']
    rw [he,measure_univ]
    exact zero_lt_one
  obtain ⟨B,hB,hbound⟩ := radial_kernel_derivative_bound (E := E) c a v hc.le hv
  let V := fun x => (-k x/v) • (y-a • x)
  have hV : Integrable V μ := by
    apply (integrable_const B).mono' (by dsimp [V,k,radialKernel]; fun_prop)
    apply ae_of_all
    intro x
    have hh := hbound x y
    simpa only [V,k,norm_smul,innerSL_apply_norm] using hh
  let C : E →L[ℝ] (E →L[ℝ] ℝ) := innerSL ℝ
  have he : (∫ x,(-k x/v) • innerSL ℝ (y-a • x) ∂μ)=innerSL ℝ (∫ x,V x ∂μ) := by
    have hh := C.integral_comp_comm hV
    simpa only [C,V,map_smul] using hh
  have hd := (radial_mixture_fderiv μ c a v hc.le hv y).log hp.ne'
  dsimp only
  refine ⟨normalized_density_probability μ k hm hi (fun x => (hpos x).le) hp,?_⟩
  have hpost := normalized_density_integral μ k hm (fun x => (hpos x).le) (p y) hp (fun x => (-1/v) • (y-a • x))
  have hv_eq : (fun x => k x • ((-1/v) • (y-a • x)))=V := by
    funext x
    dsimp [V]
    rw [smul_smul]
    congr 1
    ring
  rw [hv_eq] at hpost
  rw [hpost,map_smul]
  convert hd using 1
  rw [he]
/-- The posterior constructed from the Gaussian likelihood inherits the
prior support bound. Its mean and covariance estimates therefore do not
require any separate hypothesis on the conditional distribution. -/
theorem radial_posterior_moments {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [CompleteSpace E]
    (μ : Measure E) [IsProbabilityMeasure μ] (c a v : ℝ)
    (hc : 0<c) (hv : 0<v) (y : E) (R : ℝ) (hR : 0≤R)
    (hb : ∀ᵐ x ∂μ, ‖x‖≤R) :
    let Z := ∫ x,radialKernel c a v x y ∂μ
    let P := μ.withDensity (fun x => ENNReal.ofReal (radialKernel c a v x y/Z))
    ‖∫ x,x ∂P‖≤R ∧ ∀ h : E,
      (∫ x,⟪h,x-(∫ z,z ∂P)⟫^2 ∂P)≤R^2*‖h‖^2 := by
  let Z := ∫ x,radialKernel c a v x y ∂μ
  let P := μ.withDensity (fun x => ENNReal.ofReal (radialKernel c a v x y/Z))
  haveI : IsProbabilityMeasure P := (radial_mixture_score μ c a v hc hv y).1
  have hs : ∀ᵐ x ∂P, ‖x‖≤R :=
    normalized_density_preserves_ae μ (fun x => radialKernel c a v x y) Z
      {x | ‖x‖≤R} hb
  exact bounded_posterior_moments P R hR hs
/-- The bounded-support posterior score has the linear growth bound used
in the probability-flow equation. -/
theorem posterior_score_growth {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [CompleteSpace E]
    (P : Measure E) [IsProbabilityMeasure P] (a v R : ℝ) (hv : 0<v)
    (hR : 0≤R) (hb : ∀ᵐ x ∂P, ‖x‖≤R) (y : E) :
    (∫ x,(-1/v) • (y-a • x) ∂P)=(-1/v) • (y-a • (∫ x,x ∂P)) ∧
    ‖∫ x,(-1/v) • (y-a • x) ∂P‖≤(‖y‖+|a| * R)/v := by
  have hi : Integrable (fun x : E => x) P := by
    apply (integrable_const R).mono' (by fun_prop)
    filter_upwards [hb] with x hx
    exact hx
  have he : (∫ x,(-1/v) • (y-a • x) ∂P)=(-1/v) • (y-a • (∫ x,x ∂P)) := by
    have hia : Integrable (fun x : E => a • x) P := hi.smul a
    rw [integral_smul,integral_sub (integrable_const y) hia,
      integral_const,integral_smul]
    simp
  refine ⟨he,?_⟩
  rw [he,norm_smul,Real.norm_eq_abs,abs_div,abs_neg,abs_one,abs_of_pos hv]
  have hm := (bounded_posterior_moments P R hR hb).1
  have hn : ‖y-a • (∫ x,x ∂P)‖≤‖y‖+|a| * R := by
    apply (norm_sub_le _ _).trans
    rw [norm_smul,Real.norm_eq_abs]
    exact add_le_add_right (mul_le_mul_of_nonneg_left hm (abs_nonneg a)) _
  calc
    (1/v)*‖y-a • (∫ x,x ∂P)‖ ≤ (1/v)*(‖y‖+|a| * R) :=
      mul_le_mul_of_nonneg_left hn (by positivity)
    _ = (‖y‖+|a| * R)/v := by ring
end Asakura.Chapter9

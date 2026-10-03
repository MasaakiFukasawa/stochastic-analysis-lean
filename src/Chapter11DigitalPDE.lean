import Chapter11BarrierDelta

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal
namespace Asakura.Chapter11
open Asakura.Chapter4
set_option maxHeartbeats 2800000

noncomputable def digitalPrice (b r σ θ x : ℝ) :=
  Real.exp (-r*θ)*normalCDF (bsD b (r-σ^2/2) σ x θ)

theorem standard_gaussian_density_deriv (z : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1) (-z*gaussianPDFReal 0 1 z) z := by
  have hh := ((((hasDerivAt_id z).pow 2).neg.div_const 2).exp).const_mul ((Real.sqrt (2*Real.pi))⁻¹)
  convert hh using 1
  · funext x
    simp only [gaussianPDFReal,NNReal.coe_one,mul_one,sub_zero,Pi.neg_apply,Pi.pow_apply,id_eq]
  · simp only [gaussianPDFReal,NNReal.coe_one,mul_one,sub_zero,id_eq,Nat.reduceSub,pow_one,Nat.cast_ofNat,Pi.neg_apply,Pi.pow_apply]
    ring

theorem digital_price_theta (b r σ θ x : ℝ) (hσ : 0<σ) (hθ : 0<θ) :
    HasDerivAt (fun t => digitalPrice b r σ t x)
      (Real.exp (-r*θ)*(-r*normalCDF (bsD b (r-σ^2/2) σ x θ)+
        gaussianPDFReal 0 1 (bsD b (r-σ^2/2) σ x θ)*
          ((r-σ^2/2)/(σ*Real.sqrt θ)-(Real.log (x/b)+(r-σ^2/2)*θ)/(2*σ*(Real.sqrt θ)^3)))) θ := by
  have hh := (((hasDerivAt_id θ).const_mul (-r)).exp).mul
    ((normalCDF_hasDerivAt _).comp θ (bsD_time_derivative b (r-σ^2/2) σ x θ hσ hθ))
  convert hh using 1
  · rfl
  · simp only [Function.comp_def,id_eq,mul_one]
    ring

theorem digital_price_gamma (b r σ θ x : ℝ) (hb : 0<b) (hx : 0<x)
    (hσ : 0<σ) (hθ : 0<θ) :
    HasDerivAt (fun y => Real.exp (-r*θ)/(y*σ*Real.sqrt θ)*gaussianPDFReal 0 1 (bsD b (r-σ^2/2) σ y θ))
      (-Real.exp (-r*θ)*gaussianPDFReal 0 1 (bsD b (r-σ^2/2) σ x θ)/
        (x^2*σ*Real.sqrt θ)*(1+bsD b (r-σ^2/2) σ x θ/(σ*Real.sqrt θ))) x := by
  have hd := ((hasDerivAt_id x).mul_const σ).mul_const (Real.sqrt θ)
  have hp := (standard_gaussian_density_deriv _).comp x
    (bsD_spatial_derivative b (r-σ^2/2) σ x θ hb.ne' hx.ne')
  have hh := ((hasDerivAt_const x (Real.exp (-r*θ))).div hd (by positivity)).mul hp
  convert hh using 1
  · rfl
  · simp only [Function.comp_def,id_eq,mul_one,zero_mul,zero_sub,Pi.div_apply,Pi.mul_apply]
    field_simp
    ring

/-- The digital payoff is discontinuous, but its price is an actual smooth
solution at positive time-to-maturity. -/
theorem digital_price_pde (b r σ θ x : ℝ) (hb : 0<b) (hx : 0<x)
    (hσ : 0<σ) (hθ : 0<θ) :
    deriv (fun t => digitalPrice b r σ t x) θ+r*digitalPrice b r σ θ x=
      r*x*deriv (digitalPrice b r σ θ) x+
        σ^2*x^2*deriv (fun y => deriv (digitalPrice b r σ θ) y) x/2 := by
  have he : (fun y => deriv (digitalPrice b r σ θ) y)=ᶠ[𝓝 x]
      (fun y => Real.exp (-r*θ)/(y*σ*Real.sqrt θ)*gaussianPDFReal 0 1 (bsD b (r-σ^2/2) σ y θ)) := by
    filter_upwards [eventually_gt_nhds hx] with y hy
    exact (barrier_digital_delta b r σ θ y hb.ne' hy.ne').deriv
  have hd : deriv (digitalPrice b r σ θ) x=Real.exp (-r*θ)/(x*σ*Real.sqrt θ)*gaussianPDFReal 0 1 (bsD b (r-σ^2/2) σ x θ) :=
    (barrier_digital_delta b r σ θ x hb.ne' hx.ne').deriv
  rw [(digital_price_theta b r σ θ x hσ hθ).deriv,
    hd,he.deriv_eq,
    (digital_price_gamma b r σ θ x hb hx hσ hθ).deriv]
  dsimp only [digitalPrice,bsD]
  have hsq := Real.sq_sqrt hθ.le
  have hn : Real.sqrt θ≠0 := (Real.sqrt_pos.mpr hθ).ne'
  field_simp
  nlinarith [hsq]

end Asakura.Chapter11

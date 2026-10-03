import Chapter4BlackScholesAlgebra
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace Asakura.Chapter4
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/-- The actual standard normal distribution function, defined by its law. -/
noncomputable def normalCDF (x : ℝ) : ℝ := (gaussianReal 0 1).real (Iic x)

theorem normalCDF_eq_integral (x : ℝ) :
    normalCDF x = ∫ z in Iic x, gaussianPDFReal 0 1 z := by
  rw [normalCDF,Measure.real,gaussianReal_apply_eq_integral 0 (by norm_num)]
  exact ENNReal.toReal_ofReal (integral_nonneg (fun z => gaussianPDFReal_nonneg 0 1 z))

theorem normalCDF_hasDerivAt (x : ℝ) : HasDerivAt normalCDF (gaussianPDFReal 0 1 x) x := by
  have hc : Continuous (gaussianPDFReal 0 1) := by unfold gaussianPDFReal; fun_prop
  have hi := integrable_gaussianPDFReal 0 1
  have he : normalCDF = fun y => normalCDF 0+∫ z in 0..y, gaussianPDFReal 0 1 z := by
    funext y
    rw [normalCDF_eq_integral,normalCDF_eq_integral]
    have h := intervalIntegral.integral_Iic_sub_Iic (hi.integrableOn (s := Iic 0))
      (hi.integrableOn (s := Iic y))
    linarith
  rw [he]
  exact (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 x)
    (hc.stronglyMeasurableAtFilter volume (nhds x)) hc.continuousAt).const_add _

noncomputable def bsD (K b σ s t : ℝ) := (Real.log (s/K)+b*t)/(σ*Real.sqrt t)
noncomputable def bsCall (K r q σ s t : ℝ) :=
  Real.exp (-q*t)*s*normalCDF (bsD K (r-q+σ^2/2) σ s t)-
    Real.exp (-r*t)*K*normalCDF (bsD K (r-q-σ^2/2) σ s t)

theorem bsD_spatial_derivative (K b σ s t : ℝ)
    (hK : K ≠ 0) (hs : s ≠ 0) :
    HasDerivAt (fun s => bsD K b σ s t) (1/(s*σ*Real.sqrt t)) s := by
  have h := (((Real.hasDerivAt_log (div_ne_zero hs hK)).comp s
    ((hasDerivAt_id s).div_const K)).add_const (b*t)).div_const (σ*Real.sqrt t)
  convert h using 1
  · rfl
  · field_simp

theorem bs_discounted_density (s K r q σ t : ℝ)
    (hs : 0 < s) (hK : 0 < K) (hσ : 0 < σ) (ht : 0 < t) :
    Real.exp (-q*t)*s*gaussianPDFReal 0 1 (bsD K (r-q+σ^2/2) σ s t) =
      Real.exp (-r*t)*K*gaussianPDFReal 0 1 (bsD K (r-q-σ^2/2) σ s t) := by
  have h := black_scholes_density_identity s K r q σ t hs hK hσ ht
  dsimp only at h
  have he : Real.exp (-r*t)*Real.exp ((r-q)*t) = Real.exp (-q*t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hh := congrArg (fun x : ℝ => Real.exp (-r*t)*(Real.sqrt (2*Real.pi))⁻¹*x) h
  simpa only [gaussianPDFReal,bsD,NNReal.coe_one,mul_one,sub_zero] using
    (show Real.exp (-q*t)*s*((Real.sqrt (2*Real.pi))⁻¹*Real.exp
      (-((Real.log (s/K)+(r-q+σ^2/2)*t)/(σ*Real.sqrt t))^2/2)) =
        Real.exp (-r*t)*K*((Real.sqrt (2*Real.pi))⁻¹*Real.exp
      (-((Real.log (s/K)+(r-q-σ^2/2)*t)/(σ*Real.sqrt t))^2/2)) from by
        rw [← he]
        nlinarith only [hh])

theorem bs_call_delta (s K r q σ t : ℝ)
    (hs : 0 < s) (hK : 0 < K) (hσ : 0 < σ) (ht : 0 < t) :
    HasDerivAt (fun s => bsCall K r q σ s t)
      (Real.exp (-q*t)*normalCDF (bsD K (r-q+σ^2/2) σ s t)) s := by
  have hp := (normalCDF_hasDerivAt _).comp s
    (bsD_spatial_derivative K (r-q+σ^2/2) σ s t hK.ne' hs.ne')
  have hm := (normalCDF_hasDerivAt _).comp s
    (bsD_spatial_derivative K (r-q-σ^2/2) σ s t hK.ne' hs.ne')
  have h := (((hasDerivAt_id s).const_mul (Real.exp (-q*t))).mul hp).sub
    (hm.const_mul (Real.exp (-r*t)*K))
  convert h using 1
  · rfl
  · have hd := bs_discounted_density s K r q σ t hs hK hσ ht
    simp only [Function.comp_apply,id_eq,mul_one]
    nlinarith [congrArg (fun x : ℝ => x*(1/(s*σ*Real.sqrt t))) hd]

theorem bs_call_gamma (s K r q σ t : ℝ)
    (hs : 0 < s) (hK : 0 < K) (hσ : 0 < σ) (ht : 0 < t) :
    HasDerivAt (fun s => Real.exp (-q*t)*normalCDF (bsD K (r-q+σ^2/2) σ s t))
      (Real.exp (-q*t)*gaussianPDFReal 0 1 (bsD K (r-q+σ^2/2) σ s t)/(s*σ*Real.sqrt t)) s := by
  have h := ((normalCDF_hasDerivAt _).comp s
    (bsD_spatial_derivative K (r-q+σ^2/2) σ s t hK.ne' hs.ne')).const_mul (Real.exp (-q*t))
  convert h using 1
  · rfl
  · ring

theorem bsD_time_derivative (K b σ s t : ℝ) (hσ : 0 < σ) (ht : 0 < t) :
    HasDerivAt (fun t => bsD K b σ s t)
      (b/(σ*Real.sqrt t)-(Real.log (s/K)+b*t)/(2*σ*(Real.sqrt t)^3)) t := by
  have h := ((hasDerivAt_const t (Real.log (s/K))).add ((hasDerivAt_id t).const_mul b)).div
    ((Real.hasDerivAt_sqrt ht.ne').const_mul σ) (by positivity : σ*Real.sqrt t ≠ 0)
  convert h using 1
  · rfl
  · have hsn : Real.sqrt t ≠ 0 := by positivity
    simp only [Pi.add_apply,id_eq,mul_one,zero_add]
    field_simp

theorem bsD_time_derivative_difference (K r q σ s t : ℝ) (hσ : 0 < σ) (ht : 0 < t) :
    ((r-q+σ^2/2)/(σ*Real.sqrt t)-(Real.log (s/K)+(r-q+σ^2/2)*t)/(2*σ*(Real.sqrt t)^3))-
    ((r-q-σ^2/2)/(σ*Real.sqrt t)-(Real.log (s/K)+(r-q-σ^2/2)*t)/(2*σ*(Real.sqrt t)^3)) =
      σ/(2*Real.sqrt t) := by
  have hsn : Real.sqrt t ≠ 0 := by positivity
  have hsq := Real.sq_sqrt ht.le
  field_simp
  nlinarith [hsq]

theorem bs_call_theta (s K r q σ t : ℝ)
    (hs : 0 < s) (hK : 0 < K) (hσ : 0 < σ) (ht : 0 < t) :
    HasDerivAt (fun t => bsCall K r q σ s t)
      (-q*s*Real.exp (-q*t)*normalCDF (bsD K (r-q+σ^2/2) σ s t)+
        r*K*Real.exp (-r*t)*normalCDF (bsD K (r-q-σ^2/2) σ s t)+
        s*σ*Real.exp (-q*t)*gaussianPDFReal 0 1 (bsD K (r-q+σ^2/2) σ s t)/(2*Real.sqrt t)) t := by
  let u := (r-q+σ^2/2)/(σ*Real.sqrt t)-(Real.log (s/K)+(r-q+σ^2/2)*t)/(2*σ*(Real.sqrt t)^3)
  let v := (r-q-σ^2/2)/(σ*Real.sqrt t)-(Real.log (s/K)+(r-q-σ^2/2)*t)/(2*σ*(Real.sqrt t)^3)
  have hp := (normalCDF_hasDerivAt _).comp t (bsD_time_derivative K (r-q+σ^2/2) σ s t hσ ht)
  have hm := (normalCDF_hasDerivAt _).comp t (bsD_time_derivative K (r-q-σ^2/2) σ s t hσ ht)
  have h := ((((hasDerivAt_id t).const_mul (-q)).exp.mul_const s).mul hp).sub
    ((((hasDerivAt_id t).const_mul (-r)).exp.mul_const K).mul hm)
  have hd := bs_discounted_density s K r q σ t hs hK hσ ht
  have huv : u-v = σ/(2*Real.sqrt t) := bsD_time_derivative_difference K r q σ s t hσ ht
  have he : Real.exp (-q*t)*s*gaussianPDFReal 0 1 (bsD K (r-q+σ^2/2) σ s t)*u-
      Real.exp (-r*t)*K*gaussianPDFReal 0 1 (bsD K (r-q-σ^2/2) σ s t)*v =
      Real.exp (-q*t)*s*gaussianPDFReal 0 1 (bsD K (r-q+σ^2/2) σ s t)*(σ/(2*Real.sqrt t)) := by
    rw [← hd,← mul_sub,huv]
  convert h using 1
  · rfl
  · simp only [Function.comp_apply,id_eq,mul_one]
    change _ =
      (Real.exp (-q*t)*(-q)*s*normalCDF (bsD K (r-q+σ^2/2) σ s t)+
        Real.exp (-q*t)*s*(gaussianPDFReal 0 1 (bsD K (r-q+σ^2/2) σ s t)*u))-
      (Real.exp (-r*t)*(-r)*K*normalCDF (bsD K (r-q-σ^2/2) σ s t)+
        Real.exp (-r*t)*K*(gaussianPDFReal 0 1 (bsD K (r-q-σ^2/2) σ s t)*v))
    linear_combination -he

/-- The call formula itself satisfies the printed PDE. The derivatives here
are actual derivatives of the formula, with the normal distribution function
coming from the Gaussian measure, not supplied Greek identities. -/
theorem bs_call_pde (s K r q σ t : ℝ)
    (hs : 0 < s) (hK : 0 < K) (hσ : 0 < σ) (ht : 0 < t) :
    deriv (fun t => bsCall K r q σ s t) t+r*bsCall K r q σ s t =
      (r-q)*s*deriv (fun s => bsCall K r q σ s t) s+
        σ^2*s^2*deriv (fun s => deriv (fun x => bsCall K r q σ x t) s) s/2 := by
  have he : (fun x => deriv (fun s => bsCall K r q σ s t) x) =ᶠ[nhds s]
      (fun x => Real.exp (-q*t)*normalCDF (bsD K (r-q+σ^2/2) σ x t)) := by
    filter_upwards [eventually_gt_nhds hs] with x hx
    exact (bs_call_delta x K r q σ t hx hK hσ ht).deriv
  have hg := (bs_call_gamma s K r q σ t hs hK hσ ht).congr_of_eventuallyEq he
  rw [(bs_call_theta s K r q σ t hs hK hσ ht).deriv,
    (bs_call_delta s K r q σ t hs hK hσ ht).deriv,hg.deriv]
  exact black_scholes_pde_cancellation s K r q σ t
    (normalCDF (bsD K (r-q+σ^2/2) σ s t))
    (normalCDF (bsD K (r-q-σ^2/2) σ s t))
    (gaussianPDFReal 0 1 (bsD K (r-q+σ^2/2) σ s t)) hσ.ne' hs.ne' ht

theorem normalCDF_neg (x : ℝ) : normalCDF (-x) = 1-normalCDF x := by
  let ν := gaussianReal 0 1
  let : NullSingletonClass ν := nullSingletonClass_gaussianReal (by norm_num)
  have hsym : ν.map (fun z : ℝ => -z) = ν := by
    simpa only [neg_zero,ν] using (gaussianReal_map_neg (μ := 0) (v := 1))
  have he : ν (Iic (-x)) = ν (Ici x) := by
    conv_lhs => rw [← hsym,Measure.map_apply (by fun_prop) measurableSet_Iic]
    congr 1
    ext y
    simp
  change (ν (Iic (-x))).toReal = 1-(ν (Iic x)).toReal
  rw [he,← measure_congr (Ioi_ae_eq_Ici (μ := ν) (a := x))]
  have h := measureReal_compl (μ := ν) (s := Iic x) measurableSet_Iic
  simpa only [compl_Iic,Measure.real,measure_univ,ENNReal.toReal_one] using h

noncomputable def bsPut (K r q σ s t : ℝ) :=
  Real.exp (-r*t)*K*normalCDF (-bsD K (r-q-σ^2/2) σ s t)-
    Real.exp (-q*t)*s*normalCDF (-bsD K (r-q+σ^2/2) σ s t)

theorem bs_put_call_parity (K r q σ s t : ℝ) :
    bsPut K r q σ s t = bsCall K r q σ s t-Real.exp (-q*t)*s+Real.exp (-r*t)*K := by
  simp only [bsPut,bsCall,normalCDF_neg]
  ring

theorem bs_put_delta (s K r q σ t : ℝ)
    (hs : 0 < s) (hK : 0 < K) (hσ : 0 < σ) (ht : 0 < t) :
    HasDerivAt (fun s => bsPut K r q σ s t)
      (Real.exp (-q*t)*normalCDF (bsD K (r-q+σ^2/2) σ s t)-Real.exp (-q*t)) s := by
  simpa only [bs_put_call_parity,mul_one,Pi.sub_apply,id_eq] using
    (((bs_call_delta s K r q σ t hs hK hσ ht).sub
      ((hasDerivAt_id s).const_mul (Real.exp (-q*t)))).add_const (Real.exp (-r*t)*K))

theorem bs_put_pde (s K r q σ t : ℝ)
    (hs : 0 < s) (hK : 0 < K) (hσ : 0 < σ) (ht : 0 < t) :
    deriv (fun t => bsPut K r q σ s t) t+r*bsPut K r q σ s t =
      (r-q)*s*deriv (fun s => bsPut K r q σ s t) s+
        σ^2*s^2*deriv (fun s => deriv (fun x => bsPut K r q σ x t) s) s/2 := by
  have heP : (fun x => deriv (fun s => bsPut K r q σ s t) x) =ᶠ[nhds s]
      (fun x => Real.exp (-q*t)*normalCDF (bsD K (r-q+σ^2/2) σ x t)-Real.exp (-q*t)) := by
    filter_upwards [eventually_gt_nhds hs] with x hx
    exact (bs_put_delta x K r q σ t hx hK hσ ht).deriv
  have heC : (fun x => deriv (fun s => bsCall K r q σ s t) x) =ᶠ[nhds s]
      (fun x => Real.exp (-q*t)*normalCDF (bsD K (r-q+σ^2/2) σ x t)) := by
    filter_upwards [eventually_gt_nhds hs] with x hx
    exact (bs_call_delta x K r q σ t hx hK hσ ht).deriv
  have hgP := ((bs_call_gamma s K r q σ t hs hK hσ ht).sub_const (Real.exp (-q*t))).congr_of_eventuallyEq heP
  have hgC := (bs_call_gamma s K r q σ t hs hK hσ ht).congr_of_eventuallyEq heC
  have htime := ((bs_call_theta s K r q σ t hs hK hσ ht).sub
    (((hasDerivAt_id t).const_mul (-q)).exp.mul_const s)).add
    (((hasDerivAt_id t).const_mul (-r)).exp.mul_const K)
  have heT : (fun z => bsPut K r q σ s z) =
      (fun z => bsCall K r q σ s z-Real.exp (-q*z)*s+Real.exp (-r*z)*K) := by
    funext z
    exact bs_put_call_parity K r q σ s z
  have htime' := htime.deriv
  change deriv (fun z => bsCall K r q σ s z-Real.exp (-q*z)*s+Real.exp (-r*z)*K) t = _ at htime'
  rw [← heT] at htime'
  have hbase := bs_call_pde s K r q σ t hs hK hσ ht
  rw [(bs_call_theta s K r q σ t hs hK hσ ht).deriv,
    (bs_call_delta s K r q σ t hs hK hσ ht).deriv,hgC.deriv] at hbase
  rw [htime',(bs_put_delta s K r q σ t hs hK hσ ht).deriv,hgP.deriv,bs_put_call_parity]
  simp only [id_eq,mul_one]
  linear_combination hbase

end Asakura.Chapter4

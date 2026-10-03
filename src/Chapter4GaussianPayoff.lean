import Chapter4NormalCDF

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace Asakura.Chapter4
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem normal_tail (x : ℝ) : (gaussianReal 0 1).real (Ioi x) = normalCDF (-x) := by
  rw [normalCDF_neg]
  have h := measureReal_compl (μ := gaussianReal 0 1) (s := Iic x) measurableSet_Iic
  simpa only [normalCDF,compl_Iic,probReal_univ] using h

theorem shifted_gaussian_tail (v a : ℝ) :
    ∫ z in Ioi a, gaussianPDFReal v 1 z = normalCDF (v-a) := by
  have hpdf : (gaussianReal v 1).real (Ioi a) = ∫ z in Ioi a, gaussianPDFReal v 1 z := by
    rw [Measure.real,gaussianReal_apply_eq_integral v (by norm_num)]
    exact ENNReal.toReal_ofReal (integral_nonneg (fun _ => gaussianPDFReal_nonneg _ _ _))
  rw [← hpdf]
  have hm : (gaussianReal 0 1).map (fun x => x+v) = gaussianReal v 1 := by
    simpa only [zero_add] using (gaussianReal_map_add_const (μ := 0) (v := 1) v)
  change ((gaussianReal v 1) (Ioi a)).toReal = _
  rw [← hm,Measure.map_apply (by fun_prop) measurableSet_Ioi]
  have he : (fun x : ℝ => x+v) ⁻¹' Ioi a = Ioi (a-v) := by
    ext x
    simp only [mem_preimage,mem_Ioi]
    constructor <;> intro h <;> linarith
  rw [he]
  have h := normal_tail (a-v)
  simpa only [Measure.real,neg_sub] using h

theorem gaussian_pdf_exponential_tilt (v z : ℝ) :
    gaussianPDFReal 0 1 z*Real.exp (v*z) = Real.exp (v^2/2)*gaussianPDFReal v 1 z := by
  simp only [gaussianPDFReal,NNReal.coe_one,mul_one,sub_zero]
  rw [mul_assoc,← Real.exp_add]
  rw [mul_left_comm (Real.exp (v^2/2)),← Real.exp_add]
  congr 2
  ring

theorem gaussian_truncated_exponential (v a : ℝ) :
    (∫ z in Ioi a, Real.exp (v*z) ∂gaussianReal 0 1) =
      Real.exp (v^2/2)*normalCDF (v-a) := by
  rw [gaussianReal_of_var_ne_zero 0 (by norm_num)]
  rw [setIntegral_withDensity_eq_setIntegral_toReal_smul
    (measurable_gaussianPDF 0 1) (by exact .of_forall (fun _ => by simp [gaussianPDF])) _ measurableSet_Ioi]
  simp only [toReal_gaussianPDF,smul_eq_mul,gaussian_pdf_exponential_tilt]
  rw [integral_const_mul,shifted_gaussian_tail]

/-- Direct evaluation of the lognormal call payoff, including the
integrability needed to split the payoff into its two terms. -/
theorem lognormal_call_payoff (s K m v a : ℝ) (hs : 0 < s) (hv : 0 < v)
    (hK : K = s*Real.exp (m+v*a)) :
    (∫ z, max 0 (s*Real.exp (m+v*z)-K) ∂gaussianReal 0 1) =
      s*Real.exp (m+v^2/2)*normalCDF (v-a)-K*normalCDF (-a) := by
  have hi : Integrable (fun z => s*Real.exp (m+v*z)) (gaussianReal 0 1) := by
    simpa only [Real.exp_add,mul_assoc] using
      (integrable_exp_mul_gaussianReal (μ := 0) (v := 1) v).const_mul (s*Real.exp m)
  have he : (fun z => max 0 (s*Real.exp (m+v*z)-K)) =
      (Ioi a).indicator (fun z => s*Real.exp (m+v*z)-K) := by
    funext z
    by_cases hz : a < z
    · rw [Set.indicator_of_mem (show z ∈ Ioi a from hz),max_eq_right]
      rw [hK]
      have h := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
        (show m+v*a ≤ m+v*z by nlinarith)) hs.le
      linarith
    · rw [Set.indicator_of_notMem (show z ∉ Ioi a from hz),max_eq_left]
      rw [hK]
      have h := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
        (show m+v*z ≤ m+v*a by nlinarith)) hs.le
      linarith
  rw [he,integral_indicator measurableSet_Ioi,
    integral_sub hi.integrableOn (integrable_const K).integrableOn]
  simp only [Real.exp_add,mul_assoc]
  rw [integral_const_mul,integral_const_mul,gaussian_truncated_exponential,integral_const]
  have htail : ((gaussianReal 0 1).restrict (Ioi a)).real univ = normalCDF (-a) := by
    simpa only [Measure.real,Measure.restrict_apply_univ] using normal_tail a
  rw [htail]
  simp only [smul_eq_mul]
  ring

/-- The Gaussian expectation of the explicit geometric-Brownian terminal
value is exactly the printed call formula. -/
theorem bs_call_gaussian_payoff (s K r q σ t : ℝ)
    (hs : 0 < s) (hK : 0 < K) (hσ : 0 < σ) (ht : 0 < t) :
    (∫ z, Real.exp (-r*t)*max 0
      (s*Real.exp ((r-q-σ^2/2)*t+σ*Real.sqrt t*z)-K) ∂gaussianReal 0 1) =
      bsCall K r q σ s t := by
  let m := (r-q-σ^2/2)*t
  let v := σ*Real.sqrt t
  let a := -(Real.log (s/K)+m)/v
  have hv : 0 < v := by dsimp [v]; positivity
  have hK' : K = s*Real.exp (m+v*a) := by
    have he : m+v*a = -Real.log (s/K) := by dsimp [a]; field_simp; ring
    rw [he,Real.exp_neg,Real.exp_log (div_pos hs hK)]
    field_simp
  have h := lognormal_call_payoff s K m v a hs hv hK'
  have hsq := Real.sq_sqrt ht.le
  have hmean : m+v^2/2 = (r-q)*t := by dsimp [m,v]; nlinarith [hsq]
  have hdm : -a = bsD K (r-q-σ^2/2) σ s t := by dsimp [a,m,v,bsD]; ring
  have hdp : v-a = bsD K (r-q+σ^2/2) σ s t := by
    dsimp [a,m,v,bsD]
    field_simp
    nlinarith [hsq]
  rw [integral_const_mul]
  change Real.exp (-r*t)*(∫ z, max 0 (s*Real.exp (m+v*z)-K) ∂gaussianReal 0 1) = _
  rw [h,hmean,hdm,hdp]
  have he : Real.exp (-r*t)*Real.exp ((r-q)*t) = Real.exp (-q*t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  dsimp only [bsCall]
  linear_combination s*normalCDF (bsD K (r-q+σ^2/2) σ s t)*he

theorem bs_put_gaussian_payoff (s K r q σ t : ℝ)
    (hs : 0 < s) (hK : 0 < K) (hσ : 0 < σ) (ht : 0 < t) :
    (∫ z, Real.exp (-r*t)*max 0
      (K-s*Real.exp ((r-q-σ^2/2)*t+σ*Real.sqrt t*z)) ∂gaussianReal 0 1) =
      bsPut K r q σ s t := by
  let m := (r-q-σ^2/2)*t
  let v := σ*Real.sqrt t
  let S := fun z => s*Real.exp (m+v*z)
  have hi : Integrable S (gaussianReal 0 1) := by
    simpa only [S,Real.exp_add,mul_assoc] using
      (integrable_exp_mul_gaussianReal (μ := 0) (v := 1) v).const_mul (s*Real.exp m)
  have hc : Integrable (fun z => max 0 (S z-K)) (gaussianReal 0 1) :=
    (integrable_const 0).sup (hi.sub (integrable_const K))
  have hmean : (∫ z, S z ∂gaussianReal 0 1) = s*Real.exp ((r-q)*t) := by
    have hmgf := congrFun (mgf_fun_id_gaussianReal (μ := 0) (v := 1)) v
    simp only [mgf,zero_mul,NNReal.coe_one,one_mul,zero_add] at hmgf
    dsimp only [S]
    simp only [Real.exp_add,mul_assoc]
    rw [integral_const_mul,integral_const_mul,hmgf,← Real.exp_add]
    congr 2
    dsimp [m,v]
    nlinarith [Real.sq_sqrt ht.le]
  have he : (fun z => max 0 (K-S z)) = (fun z => max 0 (S z-K)-S z+K) := by
    funext z
    by_cases hz : S z ≤ K
    · rw [max_eq_right (sub_nonneg.mpr hz),max_eq_left (sub_nonpos.mpr hz)]
      ring
    · have hz' := (not_le.mp hz).le
      rw [max_eq_left (sub_nonpos.mpr hz'),max_eq_right (sub_nonneg.mpr hz')]
      ring
  have hcall := bs_call_gaussian_payoff s K r q σ t hs hK hσ ht
  rw [integral_const_mul] at hcall
  change Real.exp (-r*t)*(∫ z, max 0 (S z-K) ∂gaussianReal 0 1) = _ at hcall
  rw [integral_const_mul]
  change Real.exp (-r*t)*(∫ z, max 0 (K-S z) ∂gaussianReal 0 1) = _
  rw [he,integral_add (f := fun z => max 0 (S z-K)-S z) (g := fun _ => K)
    (hc.sub hi) (integrable_const K),integral_sub hc hi,hmean,
    integral_const,bs_put_call_parity]
  simp only [probReal_univ,one_smul]
  have hexp : Real.exp (-r*t)*Real.exp ((r-q)*t) = Real.exp (-q*t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  linear_combination hcall-s*hexp

/-- Transfer both directly evaluated payoff integrals to a random variable
with the standard normal law. The law itself remains an explicit premise. -/
theorem bs_payoffs_of_normal_law
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (G : Ω → ℝ)
    (hG : HasLaw G (gaussianReal 0 1) P)
    (s K r q σ t : ℝ) (hs : 0 < s) (hK : 0 < K) (hσ : 0 < σ) (ht : 0 < t) :
    (∫ ω, Real.exp (-r*t)*max 0
      (s*Real.exp ((r-q-σ^2/2)*t+σ*Real.sqrt t*G ω)-K) ∂P) = bsCall K r q σ s t ∧
    (∫ ω, Real.exp (-r*t)*max 0
      (K-s*Real.exp ((r-q-σ^2/2)*t+σ*Real.sqrt t*G ω)) ∂P) = bsPut K r q σ s t := by
  constructor
  · calc
      _ = ∫ z, Real.exp (-r*t)*max 0
          (s*Real.exp ((r-q-σ^2/2)*t+σ*Real.sqrt t*z)-K) ∂gaussianReal 0 1 :=
        hG.integral_comp (by fun_prop)
      _ = _ := bs_call_gaussian_payoff s K r q σ t hs hK hσ ht
  · calc
      _ = ∫ z, Real.exp (-r*t)*max 0
          (K-s*Real.exp ((r-q-σ^2/2)*t+σ*Real.sqrt t*z)) ∂gaussianReal 0 1 :=
        hG.integral_comp (by fun_prop)
      _ = _ := bs_put_gaussian_payoff s K r q σ t hs hK hσ ht

/-- At zero maturity the displayed formula cannot be used without a separate
continuous extension. This counterexample concerns the raw formula only. -/
theorem bs_raw_zero_time_counterexample :
    bsCall 1 0 0 1 2 0 ≠ max (0:ℝ) (2-1) := by
  have hzero : normalCDF 0 = 1/2 := by
    have h := normalCDF_neg 0
    simp only [neg_zero] at h
    linarith
  norm_num [bsCall,bsD,hzero]

end Asakura.Chapter4

import Chapter11EuropeanConditional
import Chapter4BlackScholesConstructed

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5
set_option maxHeartbeats 3300000
set_option backward.isDefEq.respectTransparency false

/-- The mean-one calculation in the book, using the Gaussian exponential
moment directly, including the zero-time case. -/
theorem brownian_exponential_mean_gaussian {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (c t : ℝ) (ht : 0≤t) :
    Integrable (fun w => Real.exp (c*B.W 0 (realTimeClamp t) w-c^2*t/2)) P ∧
      (∫ w,Real.exp (c*B.W 0 (realTimeClamp t) w-c^2*t/2) ∂P)=1 := by
  by_cases ht0 : t=0
  · subst t
    have hz : realTimeClamp (T:=(⊤:EReal)) 0=⊥ := by
      apply Subtype.ext
      simpa using real_time_clamp_eq (T:=(⊤:EReal)) 0 le_rfl le_top
    have he : (fun w => Real.exp (c*B.W 0 (realTimeClamp 0) w-c^2*0/2))=ᵐ[P] fun _ => (1:ℝ) := by
      filter_upwards [(B.martingale 0).initial P B.F] with w hw
      simp only [hz,hw,Pi.zero_apply,mul_zero,zero_div,sub_zero,Real.exp_zero]
    exact ⟨(integrable_const 1).congr he.symm,by rw [integral_congr_ae he];simp⟩
  have htp : 0<t := lt_of_le_of_ne ht (Ne.symm ht0)
  have hl := brownian_standardized_law P (T:=(⊤:EReal)) (by simp) B.F B.mono B.le B.null
    (B.W 0) (B.C 0 0) (B.martingale 0) (B.cov 0 0) (fun w r hr _ => B.diagonal_clock 0 w r hr) t htp (EReal.coe_lt_top t)
  let f := fun z : ℝ => Real.exp (-c^2*t/2)*Real.exp ((c*Real.sqrt t)*z)
  have hf : Integrable f (gaussianReal 0 1) := (integrable_exp_mul_gaussianReal (μ:=0) (v:=1) (c*Real.sqrt t)).const_mul _
  have hfm : Measurable f := by dsimp only [f];fun_prop
  have he w : f (B.W 0 (realTimeClamp t) w/Real.sqrt t)=Real.exp (c*B.W 0 (realTimeClamp t) w-c^2*t/2) := by
    dsimp only [f]
    rw [←Real.exp_add]
    congr 1
    field_simp [Real.sqrt_ne_zero'.mpr htp]
    ring
  have hi' : Integrable (fun w => f (B.W 0 (realTimeClamp t) w/Real.sqrt t)) P :=
    (integrable_map_measure hfm.aestronglyMeasurable hl.aemeasurable).mp (by rwa [hl.map_eq])
  have hmean := congrFun (mgf_fun_id_gaussianReal (μ:=0) (v:=1)) (c*Real.sqrt t)
  simp only [mgf,zero_mul,NNReal.coe_one,one_mul,zero_add] at hmean
  have hI := hl.integral_comp hfm.aestronglyMeasurable
  change (∫ w, f (B.W 0 (realTimeClamp t) w / Real.sqrt t) ∂P) = _ at hI
  simp only [he] at hI
  refine ⟨by simpa only [he] using hi',?_⟩
  rw [hI]
  dsimp only [f]
  rw [integral_const_mul,hmean,←Real.exp_add]
  convert Real.exp_zero using 1
  congr 1
  nlinarith [Real.sq_sqrt ht]

/-- The martingale step in the printed proof follows from independent
Gaussian increments, rather than invoking a separate exponential theorem. -/
theorem brownian_exponential_conditional_gaussian {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (c s t : ℝ) (hs : 0≤s) (hst : s≤t) :
    P[(fun w => Real.exp (c*B.W 0 (realTimeClamp t) w-c^2*t/2))|B.F (realTimeClamp s)]=ᵐ[P]
      fun w => Real.exp (c*B.W 0 (realTimeClamp s) w-c^2*s/2) := by
  have hi := (brownian_exponential_mean_gaussian P B c t (hs.trans hst)).1
  have hi' : Integrable (fun w => Real.exp (0+(-c^2/2)*t+c*B.W 0 (realTimeClamp t) w)) P := by
    convert hi using 1
    funext w
    congr 1
    ring
  have hCE := brownian_log_payoff_conditional P B Real.exp Real.measurable_exp 0 (-c^2/2) c t s hs hst hi'
  have hfun : (fun w => Real.exp (0+(-c^2/2)*t+c*B.W 0 (realTimeClamp t) w))=
      (fun w => Real.exp (c*B.W 0 (realTimeClamp t) w-c^2*t/2)) := by funext w;congr 1;ring
  rw [hfun] at hCE
  filter_upwards [hCE] with w hw
  rw [hw]
  have hm := congrFun (mgf_fun_id_gaussianReal (μ:=0) (v:=1)) (c*Real.sqrt (t-s))
  simp only [mgf,zero_mul,NNReal.coe_one,one_mul,zero_add] at hm
  rw [show (fun z => Real.exp (0+(-c^2/2)*s+c*B.W 0 (realTimeClamp s) w+(-c^2/2)*(t-s)+c*Real.sqrt (t-s)*z))=
    (fun z => Real.exp (c*B.W 0 (realTimeClamp s) w-c^2*t/2)*Real.exp ((c*Real.sqrt (t-s))*z)) by
      funext z;rw [←Real.exp_add];congr 1;ring]
  rw [integral_const_mul,hm,←Real.exp_add]
  congr 1
  nlinarith [Real.sq_sqrt (sub_nonneg.mpr hst)]

end Asakura.Chapter11

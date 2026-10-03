import Chapter6ExponentialLocal
import Chapter6FiniteTimeDensity
import Chapter3OpenPathMeasurable
import Chapter4FinitePathLift

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter13
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter6
set_option maxHeartbeats 3600000
set_option backward.isDefEq.respectTransparency false

theorem exponential_ito_time_density {Ω:Type*} {m:MeasurableSpace Ω}
    (P:Measure Ω) [IsProbabilityMeasure P] {T:EReal} [Fact (0≤T)] (hT:0<T)
    (F:ClosedTime T → MeasurableSpace Ω) (hF:Monotone F) (hle:∀t,F t≤m)
    (hnull:∀t N,MeasurableSet[m] N → P N=0 → MeasurableSet[F t] N)
    (X A M C:ClosedTime T → Ω → ℝ) (hX:SemimartingaleDecomposition P F X A M)
    (hC:LocalCovarianceWitness P F M M C)
    (a q:Ω × ℝ → ℝ) (ham:∀w,Measurable (fun r => a (w,r))) (hqm:∀w,Measurable (fun r => q (w,r)))
    (R:ℝ) (hR:0≤R) (hRT:(R:EReal)<T)
    (hai:∀ᵐw∂P,IntervalIntegrable (fun r => a (w,r)) volume 0 R)
    (hqi:∀ᵐw∂P,IntervalIntegrable (fun r => q (w,r)) volume 0 R)
    (hAe:∀ᵐw∂P,∀r∈Icc 0 R,A (realTimeClamp r) w=A ⊥ w+∫s in 0..r,a (w,s))
    (hCe:∀ᵐw∂P,∀r∈Icc 0 R,C (realTimeClamp r) w=∫s in 0..r,q (w,s)) :
    ∃L,LocalMProcessWitness P F L ∧
      ItoCovarianceFormula P F M (fun z => Real.exp (X (realTimeClamp z.2) z.1)) L ∧
      ∀r∈Icc 0 R,(fun w => Real.exp (X (realTimeClamp r) w))=ᵐ[P]
        (fun w => Real.exp (X ⊥ w)+L (realTimeClamp r) w+
          ∫s in 0..r,Real.exp (X (realTimeClamp s) w)*(a (w,s)+q (w,s)/2)) := by
  have hCv:=covariance_adapted_variation P F hF hle hX.martingale hX.martingale hC
  have hCc w t (ht:t<⊤):ContinuousAt (fun s => C s w) t := by
    have hh:=((hX.martingale.path P F w t ht).mul (hX.martingale.path P F w t ht)).sub (hC.defect.path P F w t ht)
    convert hh using 1
    funext s
    dsimp only [Pi.sub_apply,Pi.mul_apply]
    ring
  let H:=fun t w => Real.exp (X t w)
  have hHa t (ht:t<⊤):Measurable[F t] (H t) := by
    have he:X t=fun w => A t w+M t w := funext (hX.decomposition t ht)
    exact Real.continuous_exp.measurable.comp (he ▸ ((hX.variation.adapted t ht).add (hX.martingale.adapted P F t ht)))
  have hHc w t ht:ContinuousAt (fun s => H s w) t := Real.continuous_exp.continuousAt.comp (hX.continuous w t ht)
  obtain ⟨c,hc,hcm,hcT,_,_,hcc⟩:=positive_real_time_exhaustion hT
  obtain ⟨I,L,hIL,hI,hLI⟩:=continuous_semimartingale_integral_exists P hT F hF hle hnull X A M H hX hHa hHc
    c (fun n => (hc n).le) hcm.monotone hcT hcc
  have hreg:=open_process_real_regularity F H hHa hHc
  obtain ⟨J,hJv,hJc,hJ⟩:=continuous_adapted_variation_exists P F hF hnull c (fun n => (hc n).le)
    hcm.monotone hcT hcc C hCv hCc (fun z => H (realTimeClamp z.2) z.1) hreg.1 hreg.2
  have hIto:=scalar_ito_formula P hT F hF hle hnull X A M C (fun t w => I t w+L t w) J hX hC
    Real.exp Real.contDiff_exp c (fun n => (hc n).le) hcT hcc
    (by simpa only [Real.deriv_exp] using
      (show SemimartingaleIntegralFormula P F c (fun n => (hc n).le) A M
        (fun z => H (realTimeClamp z.2) z.1) (fun t w => I t w+L t w) from ⟨I,L,hIL,hI,hLI⟩))
    (by simpa only [iteratedDeriv_eq_iterate,Real.iter_deriv_exp] using hJ)
  refine ⟨L,hIL.martingale,hLI,?_⟩
  intro r hr
  have hrT: (r:EReal)<T := (EReal.coe_le_coe hr.2).trans_lt hRT
  have hsub:uIcc 0 r⊆uIcc 0 R := by simpa only [uIcc_of_le hr.1,uIcc_of_le hR] using Icc_subset_Icc_right hr.2
  have hia:=hai.mono (fun w hw => hw.mono_set hsub)
  have hiq:=hqi.mono (fun w hw => hw.mono_set hsub)
  have hhm w:Measurable (fun s => H (realTimeClamp s) w) := open_path_real_measurable _ (hHc w)
  have hi:=finite_time_density_variation_integral P A I (A ⊥) a _ c (fun n => (hc n).le) hcT hcc r hr.1 hrT
    (hAe.mono (fun w hw s hs => hw s (Icc_subset_Icc_right hr.2 hs))) ham hia hhm (hreg.2 r hr.1 hrT) hI
  have hj:=finite_time_density_variation_integral P C J (fun _ => 0) q _ c (fun n => (hc n).le) hcT hcc r hr.1 hrT
    (by simpa only [zero_add] using hCe.mono (fun w hw s hs => hw s (Icc_subset_Icc_right hr.2 hs))) hqm hiq hhm (hreg.2 r hr.1 hrT) hJ
  filter_upwards [hIto,hi,hj,hia,hiq] with w hw hi hj hia hiq
  have hcont:ContinuousOn (fun s => H (realTimeClamp s) w) (uIcc 0 r) := by simpa only [uIcc_of_le hr.1] using hreg.2 r hr.1 hrT w
  have hprodA:=hia.continuousOn_mul hcont
  have hprodQ:=hiq.continuousOn_mul hcont
  have hh:=hw _ (real_time_below r hr.1 hrT)
  rw [hi,hj] at hh
  have hs:(∫s in 0..r,H (realTimeClamp s) w*(a (w,s)+q (w,s)/2))=
      (∫s in 0..r,H (realTimeClamp s) w*a (w,s))+(∫s in 0..r,H (realTimeClamp s) w*q (w,s))/2 := by
    simp only [mul_add,← mul_div_assoc]
    rw [intervalIntegral.integral_add hprodA (hprodQ.div_const 2),intervalIntegral.integral_div]
  change Real.exp (X (realTimeClamp r) w)=Real.exp (X ⊥ w)+L (realTimeClamp r) w+∫s in 0..r,H (realTimeClamp s) w*(a (w,s)+q (w,s)/2)
  rw [hs]
  dsimp only [H] at hh
  linarith
end Asakura.Chapter13
#print axioms Asakura.Chapter13.exponential_ito_time_density

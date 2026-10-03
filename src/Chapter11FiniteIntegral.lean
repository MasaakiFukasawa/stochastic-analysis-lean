import Chapter5InfiniteBrownianIntegral
import Chapter5ProgressiveZeroExtension
import Chapter5StoppedIntegralFormula
import Chapter4BrownianSystem

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5
set_option maxHeartbeats 3300000
set_option backward.isDefEq.respectTransparency false

theorem finite_zero_extension_L2 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (H : Ω × ℝ → ℝ) (hH : Measurable H) (T : ℝ)
    (hi : Integrable (fun z => H z^2) (P.prod (volume.restrict (Ioo 0 T)))) :
    MemLp (fun z : Ω × ℝ => (Iic T).indicator (fun r => H (z.1,r)) z.2) 2
      (P.prod (volume.restrict (Ioi 0))) := by
  have he : (P.prod (volume.restrict (Ioi (0:ℝ)))).restrict ((univ : Set Ω) ×ˢ Iic T)=
      P.prod (volume.restrict (Ioo 0 T)) := by
    rw [←Measure.prod_restrict,Measure.restrict_univ,Measure.restrict_restrict measurableSet_Iic]
    congr 1
    rw [show Iic T∩Ioi (0:ℝ)=Ioc 0 T by ext x;simp only [mem_inter_iff,mem_Iic,mem_Ioi,mem_Ioc];tauto,
      ←restrict_Ioo_eq_restrict_Ioc]
  have hL2 : MemLp H 2 ((P.prod (volume.restrict (Ioi (0:ℝ)))).restrict ((univ : Set Ω) ×ˢ Iic T)) := by
    rw [he]
    exact (memLp_two_iff_integrable_sq hH.aestronglyMeasurable).mpr hi
  have hh := (memLp_indicator_iff_restrict (MeasurableSet.univ.prod measurableSet_Iic)).mpr hL2
  convert hh using 1
  funext z
  simp only [Set.indicator,mem_prod,mem_univ,true_and,mem_Iic]

/-- A finite expected energy produces a genuine M2 integral including
maturity, by zero extension and the already constructed terminal isometry. -/
theorem finite_energy_integral_constructed {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (H : Ω × ℝ → ℝ) (hH : Measurable H) (T : ℝ) (hT : 0≤T)
    (hp : @Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) T => B.F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) T => H (z.1,z.2.val)))
    (hi : Integrable (fun z => H z^2) (P.prod (volume.restrict (Ioo 0 T)))) :
    ∃ N : HalfClosedTime → Ω → ℝ,ContinuousM2Witness P B.F N ∧ LocalMProcessWitness P B.F N ∧
      ItoCovarianceFormula P B.F (B.W 0)
        (fun z => (Iic T).indicator (fun r => H (z.1,r)) z.2) N := by
  have htop : (0:EReal)<⊤ := by simp
  obtain ⟨c,hc,hcm,hcT,hct,hcut,hcc⟩ := positive_real_time_exhaustion htop
  have hco r : ∃ n,r≤c n := by
    obtain ⟨n,hn⟩ := hcc (realTimeClamp (max r 0)) (by
      change (realTimeClamp (T:=(⊤:EReal)) (max r 0):EReal)<⊤
      rw [real_time_clamp_eq _ (le_max_right r 0) le_top]
      exact EReal.coe_lt_top _)
    change (realTimeClamp (T:=(⊤:EReal)) (max r 0):EReal)<(realTimeClamp (c n):EReal) at hn
    rw [real_time_clamp_eq _ (le_max_right r 0) le_top,real_time_clamp_eq _ (hc n).le le_top] at hn
    exact ⟨n,(le_max_left r 0).trans (EReal.coe_lt_coe_iff.mp hn).le⟩
  let G := fun z : Ω × ℝ => (Iic T).indicator (fun r => H (z.1,r)) z.2
  have hG : Measurable G := by
    change Measurable ((Prod.snd ⁻¹' Iic T).indicator H)
    exact hH.indicator (measurableSet_Iic.preimage measurable_snd)
  have hGp n := progressive_finite_zero_extension (fun r => B.F (realTimeClamp r))
    (B.mono.comp real_time_clamp_mono) T hT H hp (c n)
  obtain ⟨N,hN,hNl,hNI,_,_⟩ := brownian_infinite_terminal_integral P htop B.F B.mono B.le B.null
    (B.W 0) (B.C 0 0) (B.martingale 0) (B.cov 0 0) c hc hcm hcT hct hcut hcc
    (fun j w r hr => B.diagonal_clock 0 w r hr.1) G hG hGp hco (finite_zero_extension_L2 P H hH T hi)
  exact ⟨N,hN,hNl,hNI⟩

/-- Prefix uniqueness for general progressive integrands follows by
stopping both actual integrals and applying covariance uniqueness. -/
theorem progressive_ito_prefix_congr {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (G H : Ω × ℝ → ℝ) (hG : ∀ w,Measurable (fun r => G (w,r)))
    (hH : ∀ w,Measurable (fun r => H (w,r)))
    (N M : HalfClosedTime → Ω → ℝ) (hN : LocalMProcessWitness P B.F N) (hM : LocalMProcessWitness P B.F M)
    (hNI : ItoCovarianceFormula P B.F (B.W 0) G N) (hMI : ItoCovarianceFormula P B.F (B.W 0) H M)
    (R : ℝ) (hR : 0≤R) (he : ∀ w t,t∈Ioc 0 R → G (w,t)=H (w,t)) :
    ∀ᵐ w ∂P,∀ t,t<⊤ → N (min (realTimeClamp R) t) w=M (min (realTimeClamp R) t) w := by
  have htop : (0:EReal)<⊤ := by simp
  have hstop t : MeasurableSet[B.F t] {w : Ω | realTimeClamp (T:=(⊤:EReal)) R≤t} := by
    by_cases h : realTimeClamp (T:=(⊤:EReal)) R≤t <;> simp [h]
  have hn := stopped_ito_covariance_formula P htop B.F B.mono B.le B.null (B.W 0) N G
    (B.martingale 0) hN hG hNI R hR
  have hm := stopped_ito_covariance_formula P htop B.F B.mono B.le B.null (B.W 0) M H
    (B.martingale 0) hM hH hMI R hR
  have hei : (fun z : Ω × ℝ => (Ioc 0 R).indicator (fun r => G (z.1,r)) z.2)=
      (fun z : Ω × ℝ => (Ioc 0 R).indicator (fun r => H (z.1,r)) z.2) := by
    funext z
    by_cases hz : z.2∈Ioc 0 R
    · simp only [Set.indicator_of_mem hz,he z.1 z.2 hz]
    · simp only [Set.indicator_of_notMem hz]
  rw [hei] at hn
  exact hn.unique P htop B.F B.mono B.le B.null (B.W 0) _ _ _ (B.martingale 0)
    (hN.stopped P B.F B.mono B.le _ hstop) (hM.stopped P B.F B.mono B.le _ hstop) hm

/-- Equality of continuous processes before a finite maturity extends to
maturity on a single null-set complement, using a deterministic sequence. -/
theorem continuous_finite_endpoint_equality {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (N M : ℝ → Ω → ℝ) (T : ℝ) (hT : 0<T)
    (hN : ∀ w,ContinuousAt (fun t => N t w) T)
    (hM : ∀ w,ContinuousAt (fun t => M t w) T)
    (he : ∀ t,0<t → t<T → N t=ᵐ[P] M t) : N T=ᵐ[P] M T := by
  obtain ⟨c,hcm,hc,hlim⟩ := exists_seq_strictMono_tendsto' hT
  filter_upwards [ae_all_iff.mpr (fun n => he (c n) (hc n).1 (hc n).2)] with w hw
  have hn := (hN w).tendsto.comp hlim
  have hm := (hM w).tendsto.comp hlim
  simp only [Function.comp_def,hw] at hn
  exact tendsto_nhds_unique hn hm

end Asakura.Chapter11

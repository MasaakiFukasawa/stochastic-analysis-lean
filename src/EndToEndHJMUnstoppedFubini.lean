import Chapter13LocalParameterFubini
import Chapter13StoppedIntegralIdentification
import Chapter13M2EvaluationAE
import Chapter13ParameterIntegralCoefficients

open MeasureTheory Set
namespace Asakura.EndToEnd
open Asakura.Chapter13
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter4
set_option maxHeartbeats 5000000
set_option backward.isDefEq.respectTransparency false

/-- The unstopped HJM interchange for the original actual Ito integrals.
Localization, M2 evaluation, identification of the stopped integrals, and
removal of stopping are all proved, not supplied as interchange hypotheses. -/
theorem hjm_unstopped_fubini_ae {Ω E:Type} {m:MeasurableSpace Ω} [MeasurableSpace E]
    (P:Measure Ω) [IsProbabilityMeasure P] {d:ℕ} (B:BrownianSystem P d) (i:Fin d)
    (μ:Measure E) [IsFiniteMeasure μ]
    (H:E × (Ω × ℝ) → ℝ) (hm:Measurable H)
    (hp:∀b,0<b → @Measurable _ _
      ((inferInstance : MeasurableSpace E).prod (progressiveSpace (fun t:Icc (0:ℝ) b => B.F (realTimeClamp t.val)))) inferInstance
      (fun z:E × (Ω × Icc (0:ℝ) b) => H (z.1,(z.2.1,z.2.2.val))))
    (hb:∀w b,0≤b → ∃K:ℝ,0≤K ∧ ∀x r,r∈Icc 0 b → |H (x,(w,r))|≤K)
    (N:E → HalfClosedTime → Ω → ℝ) (hN:∀x,LocalMProcessWitness P B.F (N x))
    (hNI:∀ᵐx∂μ,ItoCovarianceFormula P B.F (B.W i) (fun z => H (x,z)) (N x))
    (hNm:Measurable (fun z:E × (Ω × HalfClosedTime) => N z.1 z.2.2 z.2.1))
    (V:HalfClosedTime → Ω → ℝ) (hV:LocalMProcessWitness P B.F V)
    (hVI:ItoCovarianceFormula P B.F (B.W i) (fun z => ∫x,H (x,z)∂μ) V) :
    ∀r,0≤r → ∀ᵐw∂P, V (realTimeClamp r) w=(∫x,N x (realTimeClamp r) w∂μ) ∧
      Integrable (fun x => N x (realTimeClamp r) w) μ := by
  intro r hr
  let R:=r+1
  have hR:0<R := by dsimp [R]; linarith
  have hrR:realTimeClamp (T:=(⊤:EReal)) r≤realTimeClamp R := real_time_clamp_mono (by dsimp [R];linarith)
  have hrt:realTimeClamp (T:=(⊤:EReal)) r<⊤ := real_time_below r hr (EReal.coe_lt_top r)
  have hT:(0:EReal)<⊤ := by simp
  obtain ⟨c,hc,hcm,hcT,hct,hcut,hcc⟩:=positive_real_time_exhaustion hT
  have hMloc (Y:HalfClosedTime → Ω → ℝ) (hY:ContinuousM2Witness P B.F Y):LocalMProcessWitness P B.F Y :=
    continuous_m2_is_local P B.F B.mono B.le (fun n => realTimeClamp (c n)) hct.monotone hcut hcc Y hY
  have hHi x w b (hb0:0≤b):IntervalIntegrable (fun s => H (x,(w,s))^2) volume 0 b := by
    apply bounded_coefficient_square (fun z => H (x,z)) (hm.comp measurable_prodMk_left) ?_ w b hb0
    intro w b hb0
    obtain ⟨K,hK,hbound⟩:=hb w b hb0
    exact ⟨K,hK,fun s hs => hbound x s hs⟩
  obtain ⟨hJm,hJp,hJi,_⟩:=parameter_integral_coefficients B.F μ H hm hp hb
  obtain ⟨τ,hτ,htop,hfib⟩:=local_parameter_fubini P B i μ R hR H hm hp (fun w => hb w R hR.le)
  have he n:∀ᵐw∂P,V (min (min (realTimeClamp R) (τ n w)) (realTimeClamp r)) w=
      (∫x,N x (min (min (realTimeClamp R) (τ n w)) (realTimeClamp r)) w∂μ) ∧
      Integrable (fun x => N x (min (min (realTimeClamp R) (τ n w)) (realTimeClamp r)) w) μ := by
    obtain ⟨Z,hZi,hZrep,Y,hY,hYI,hZe⟩:=hfib n
    let K:=fun z:Ω × ℝ => (Ioc (0:ℝ) (finitePrefixTime R hR.le (τ n z.1)).val).indicator
      (fun s => ∫x,H (x,(z.1,s))∂μ) z.2
    have hYI':ItoCovarianceFormula P B.F (B.W i) K Y := by
      convert hYI using 1
      funext z
      dsimp only [K]
      by_cases hz:z.2∈Ioc (0:ℝ) (finitePrefixTime R hR.le (τ n z.1)).val <;> simp [hz]
    have hYe:=stopped_integral_identified P B i (fun z => ∫x,H (x,z)∂μ) hJp
      (fun b hb0 => ae_of_all _ fun w => hJi w b hb0) V hV hVI R hR.le (τ n) (hτ n) Y (hMloc Y hY) hYI'
    let G:=fun z:E × Ω => N z.1 (min (min (realTimeClamp R) (τ n z.2)) (realTimeClamp r)) z.2
    have htm:Measurable (τ n) := measurable_of_Iic (fun t => B.le t _ (hτ n t))
    have hG:Measurable G := hNm.comp (measurable_fst.prodMk
      (measurable_snd.prodMk (((measurable_const.min (htm.comp measurable_snd))).min measurable_const)))
    have hrep:∀ᵐx∂μ,∃Yx:HalfClosedTime → Ω → ℝ,∃h:ContinuousM2Witness P B.F Yx,
        Z x=m2TerminalOfProcess P B.F Yx h ∧ Yx (realTimeClamp r)=ᵐ[P] (fun w => G (x,w)) := by
      filter_upwards [hZrep,hNI] with x hx hix
      obtain ⟨Yx,hYx,hYxI,hzx⟩:=hx
      refine ⟨Yx,hYx,hzx,?_⟩
      have hh:=stopped_integral_identified P B i (fun z => H (x,z))
        (fun b hb0 => (hp b hb0).comp measurable_prodMk_left)
        (fun b hb0 => ae_of_all _ fun w => hHi x w b hb0) (N x) (hN x) hix
        R hR.le (τ n) (hτ n) Yx (hMloc Yx hYx) hYxI
      exact hh.mono (fun w hw => hw _ hrt)
    have hval:=m2_fixed_time_from_realizations P B.F B.mono B.le B.null μ Z hZi G hG (realTimeClamp r) hrep Y hY hZe
    have hGi:=m2_realizations_product_integrable P B.F B.mono B.le B.null μ Z hZi G hG (realTimeClamp r) hrep
    filter_upwards [hYe,hval,hGi.prod_left_ae] with w hy hv hw
    exact ⟨(hy _ hrt).symm.trans hv,hw⟩
  filter_upwards [ae_all_iff.mpr he] with w hw
  obtain ⟨n,hn⟩:=htop w
  simpa [hn n le_rfl,min_eq_right hrR] using hw n
end Asakura.EndToEnd
#print axioms Asakura.EndToEnd.hjm_unstopped_fubini_ae

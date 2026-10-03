import Chapter11EuropeanTerminalEnergy
import Chapter11FiniteIntegral

open MeasureTheory Set Filter
open scoped Topology ContDiff ENNReal
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5
set_option maxHeartbeats 4500000
set_option backward.isDefEq.respectTransparency false

/-- The delta integral is constructed at maturity and its terminal value
is the discounted payoff. No terminal value of the integral is assumed. -/
theorem european_delta_integral_at_maturity {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (h : Ioi (0:ℝ) → ℝ) (hh : Continuous h) (hn : ∀ x,0≤h x)
    (C m : ℝ) (hC : 0≤C) (hb : ∀ x,h x≤C*(1+x.val^m))
    (s r σ T : ℝ) (hs : 0<s) (hσ : 0<σ) (hT : 0<T)
    (M : HalfClosedTime → Ω → ℝ) (hM : ContinuousM2Witness P B.F M) (a : ℝ)
    (hrep : ∀ t,(fun w => a+M t w)=ᵐ[P]
      P[(fun w => Real.exp (-r*T)*h ⟨s*Real.exp ((r-σ^2/2)*T+σ*B.W 0 (realTimeClamp T) w),mul_pos hs (Real.exp_pos _)⟩)|B.F t]) :
    let H := fun z : Ω × ℝ => fderiv ℝ (europeanBrownianPrice h s r σ T)
      ![z.2,B.W 0 (realTimeClamp z.2) z.1] (Pi.single 1 1)
    ∃ N : HalfClosedTime → Ω → ℝ,ContinuousM2Witness P B.F N ∧
      ItoCovarianceFormula P B.F (B.W 0)
        (fun z => (Iic T).indicator (fun t => H (z.1,t)) z.2) N ∧
      (∀ t∈Icc 0 T,N (realTimeClamp t)=ᵐ[P] M (realTimeClamp t)) ∧
      ((fun w => a+N (realTimeClamp T) w)=ᵐ[P]
        fun w => Real.exp (-r*T)*h ⟨s*Real.exp ((r-σ^2/2)*T+σ*B.W 0 (realTimeClamp T) w),mul_pos hs (Real.exp_pos _)⟩) := by
  dsimp only
  let v := europeanBrownianPrice h s r σ T
  let H := fun z : Ω × ℝ => fderiv ℝ v ![z.2,B.W 0 (realTimeClamp z.2) z.1] (Pi.single 1 1)
  have hm : Measurable (fun q : ℝ × ℝ => fderiv ℝ v ![q.1,q.2] (Pi.single 1 1)) := by
    apply (measurable_fderiv_apply_const (𝕜:=ℝ) (f:=v) (Pi.single 1 1)).comp
    apply Measurable.of_eval
    intro i
    fin_cases i <;> fun_prop
  have hH : Measurable H := hm.comp (measurable_snd.prodMk (half_local_joint_measurable P B.F B.le (B.W 0) (B.martingale 0)))
  have hP := borel_diffusion_progressive P B.F B.mono (B.W 0) (fun _ _ => 0) (B.W 0)
    (local_martingale_semimartingale_decomposition P (T:=(⊤:EReal)) (by simp) B.F B.mono (B.W 0) (B.martingale 0))
    T hT.le (EReal.coe_lt_top T) _ hm
  have hE := (european_delta_terminal_energy P B h hh hn C m hC hb s r σ T hs hσ hT M hM a hrep).1
  obtain ⟨N,hN,hNl,hNI⟩ := finite_energy_integral_constructed P B H hH T hT.le hP hE
  let G := fun z : Ω × ℝ => (Iic T).indicator (fun t => H (z.1,t)) z.2
  have hG : Measurable G := by
    change Measurable ((Prod.snd ⁻¹' Iic T).indicator H)
    exact hH.indicator (measurableSet_Iic.preimage measurable_snd)
  have heR R (hR : 0≤R) (hRT : R<T) : N (realTimeClamp R)=ᵐ[P] M (realTimeClamp R) := by
    obtain ⟨L,hL,hLI,heL,_,_⟩ := european_delta_prefix_energy P B h hh hn C m hC hb s r σ R T hs hσ hR hRT M hM a hrep
    let J := fun z : Ω × ℝ => fderiv ℝ v ![(finitePrefixTime (T:=(⊤:EReal)) R hR (realTimeClamp z.2)).val,
      B.W 0 (realTimeClamp z.2) z.1] (Pi.single 1 1)
    have hJ : Measurable J := by
      exact hm.comp (((continuous_subtype_val.comp ((finite_prefix_time_continuous (T:=(⊤:EReal)) R hR).comp real_time_clamp_continuous)).measurable.comp measurable_snd).prodMk
        (half_local_joint_measurable P B.F B.le (B.W 0) (B.martingale 0)))
    have heG w t (ht : t∈Ioc 0 R) : G (w,t)=J (w,t) := by
      dsimp only [G,J,H]
      rw [Set.indicator_of_mem (show t∈Iic T from (ht.2.trans hRT.le)),finite_prefix_time_of_real R t hR ⟨ht.1.le,ht.2⟩ le_top]
    have he := progressive_ito_prefix_congr P B G J
      (fun w => hG.comp measurable_prodMk_left) (fun w => hJ.comp measurable_prodMk_left)
      N L hNl hL hNI hLI R hR heG
    filter_upwards [he,heL R ⟨hR,le_rfl⟩] with w hw hwL
    have hh := hw (realTimeClamp R) (real_time_below R hR (EReal.coe_lt_top R))
    simpa only [min_self,hwL] using hh
  have heT : N (realTimeClamp T)=ᵐ[P] M (realTimeClamp T) :=
    continuous_finite_endpoint_equality P (fun t => N (realTimeClamp t)) (fun t => M (realTimeClamp t)) T hT
      (fun w => ((hN.path w).comp real_time_clamp_continuous).continuousAt)
      (fun w => ((hM.path w).comp real_time_clamp_continuous).continuousAt)
      (fun t ht htT => heR t ht.le htT)
  refine ⟨N,hN,hNI,?_,?_⟩
  · intro t ht
    rcases lt_or_eq_of_le ht.2 with hlt|heq
    · exact heR t ht.1 hlt
    · simpa only [heq] using heT
  · let U := fun w => Real.exp (-r*T)*h ⟨s*Real.exp ((r-σ^2/2)*T+σ*B.W 0 (realTimeClamp T) w),mul_pos hs (Real.exp_pos _)⟩
    have hUm : Measurable[B.F (realTimeClamp T)] U := by
      apply Measurable.const_mul
      apply hh.measurable.comp
      apply Measurable.subtype_mk
      exact (((B.martingale 0).adapted P B.F _ (real_time_below T hT.le (EReal.coe_lt_top T))).const_mul σ |>.const_add _).exp.const_mul s
    have hUi : Integrable U P := ((european_actual_terminal_L2 P B h hh C m
      (fun x => by rw [Real.norm_eq_abs,abs_of_nonneg (hn x)];exact hb x) s (r-σ^2/2) σ T hs hT).integrable (by norm_num)).const_mul _
    have hCE := condExp_of_stronglyMeasurable (B.le (realTimeClamp T)) hUm.stronglyMeasurable hUi
    have he := hrep (realTimeClamp T)
    filter_upwards [he,heT] with w hw hwt
    rw [hwt]
    exact hw.trans (congrFun hCE w)

end Asakura.Chapter11

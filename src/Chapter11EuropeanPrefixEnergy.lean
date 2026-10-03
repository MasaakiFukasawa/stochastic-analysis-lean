import Chapter11EuropeanPriceIdentification
import Chapter11OpenGradientRegularity
import Chapter11PriceIntegralIdentification
import Chapter11HedgeEnergy

open MeasureTheory Set Filter
open scoped Topology ContDiff
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5
set_option maxHeartbeats 3800000
set_option backward.isDefEq.respectTransparency false

/-- Complete preterminal connection: the Gaussian PDE price constructs the
delta integral and its energy bound using the martingale representation
already proved in the preceding subsection. -/
theorem european_delta_prefix_energy {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (h : Ioi (0:ℝ) → ℝ) (hh : Continuous h) (hn : ∀ x,0≤h x)
    (C m : ℝ) (hC : 0≤C) (hb : ∀ x,h x≤C*(1+x.val^m))
    (s r σ R T : ℝ) (hs : 0<s) (hσ : 0<σ) (hR : 0≤R) (hRT : R<T)
    (M : HalfClosedTime → Ω → ℝ) (hM : ContinuousM2Witness P B.F M) (a : ℝ)
    (hrep : ∀ t,(fun w => a+M t w)=ᵐ[P]
      P[(fun w => Real.exp (-r*T)*h ⟨s*Real.exp ((r-σ^2/2)*T+σ*B.W 0 (realTimeClamp T) w),mul_pos hs (Real.exp_pos _)⟩)|B.F t]) :
    let G := fun z : Ω × ℝ => fderiv ℝ (europeanBrownianPrice h s r σ T)
      ![(finitePrefixTime (T:=(⊤:EReal)) R hR (realTimeClamp z.2)).val,B.W 0 (realTimeClamp z.2) z.1] (Pi.single 1 1)
    ∃ N : HalfClosedTime → Ω → ℝ,LocalMProcessWitness P B.F N ∧
      ItoCovarianceFormula P B.F (B.W 0) G N ∧
      (∀ t∈Icc 0 R,N (realTimeClamp t)=ᵐ[P] M (realTimeClamp t)) ∧
      Integrable (fun w => ∫ t in 0..R,(G (w,t))^2) P ∧
      (∫ w,(∫ t in 0..R,(G (w,t))^2) ∂P)≤∫ w,(M ⊤ w)^2 ∂P := by
  dsimp only
  obtain ⟨hfc,hfn,hfb⟩ := log_payoff_regular h hh hn C m hb
  let F := fun q => ∫ z,logPayoff h z*heatLogKernel z q
  have hF : ContDiffOn ℝ ∞ F {q | 0<q.1} := exponential_payoff_heat_smooth _ hfc.measurable hfn C m hC hfb
  have hv : ContDiffOn ℝ 2 (europeanBrownianPrice h s r σ T) {q | q 0<T} := by
    intro q hq
    exact (brownian_heat_smooth_at F hF _ σ T _ hσ.ne' q hq).contDiffWithinAt.of_le (by norm_num)
  obtain ⟨N,hN,hNI,hIto⟩ := european_price_ito_constructed P B h hh hn C m hC hb s r σ R T hσ.ne' hR hRT
  have hCE t (ht : t∈Icc 0 R) := (european_price_conditional_identification P B h hh C m
    (fun x => by rw [Real.norm_eq_abs,abs_of_nonneg (hn x)];exact hb x)
    s r σ T t hs hσ ht.1 (ht.2.trans_lt hRT)).symm
  have he := (price_integral_identification P B.F _ _ N M hN hM a
    (europeanBrownianPrice h s r σ T ![0,0]) R hR hCE
    (fun t ht => hrep (realTimeClamp t)) hIto).2
  obtain ⟨_,hGp,hGi⟩ := open_price_gradient_regularity P B R T hR hRT _ hv
  obtain ⟨hi,_,hbnd⟩ := brownian_prefix_energy_of_price P B _ hGp
    (fun d hd => ae_of_all _ (hGi d hd)) N M hN hNI hM R hR he
  exact ⟨N,hN,hNI,he,hi,hbnd⟩

end Asakura.Chapter11

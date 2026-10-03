import Chapter11OpenGradientRegularity
import Chapter4StoppedBrownianIntegral
import Chapter2SquareIntegrableStop
import Chapter2StochasticFubiniPrinted

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5
set_option maxHeartbeats 3400000
set_option backward.isDefEq.respectTransparency false

theorem open_harmonic_common_representation {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (R T : ℝ) (hR : 0≤R) (hRT : R<T)
    (v : (Fin 2 → ℝ) → ℝ) (hv : ContDiffOn ℝ 2 v {q | q 0<T})
    (hpde : ∀ t∈Icc 0 R,∀ x,fderiv ℝ v ![t,x] (Pi.single 0 1)+
      fderiv ℝ (fderiv ℝ v) ![t,x] (Pi.single 1 1) (Pi.single 1 1)/2=0) :
    ∃ N : HalfClosedTime → Ω → ℝ,LocalMProcessWitness P B.F N ∧
      ItoCovarianceFormula P B.F (B.W 0)
        (fun z => fderiv ℝ v ![(finitePrefixTime (T:=(⊤:EReal)) R hR (realTimeClamp z.2)).val,
          B.W 0 (realTimeClamp z.2) z.1] (Pi.single 1 1)) N ∧
      ∀ᵐ w ∂P,∀ t∈Icc 0 R,v ![t,B.W 0 (realTimeClamp t) w]=v ![0,B.W 0 ⊥ w]+N (realTimeClamp t) w := by
  obtain ⟨N,hN,hNI,he⟩ := open_harmonic_ito_constructed P B R T hR hRT v hv hpde
  refine ⟨N,hN,hNI,?_⟩
  have htime (t : ℝ) : realTimeClamp (T:=(⊤:EReal)) t<⊤ :=
    (real_time_clamp_mono (le_max_left t 0)).trans_lt (real_time_below (max t 0) (le_max_right t 0) (EReal.coe_lt_top _))
  apply right_continuous_common_equality P R hR
  · apply ae_of_all
    intro w t ht htR
    have hvt : ContinuousAt v ![t,B.W 0 (realTimeClamp t) w] :=
      hv.continuousOn.continuousAt (isOpen_lt (continuous_apply 0) continuous_const |>.mem_nhds (by simpa using htR.trans hRT))
    apply (hvt.comp_of_eq (show ContinuousAt (fun s => ![s,B.W 0 (realTimeClamp s) w]) t from ?_) rfl).continuousWithinAt
    apply continuousAt_pi.mpr
    intro i
    fin_cases i
    · change ContinuousAt (fun s : ℝ => s) t
      exact continuousAt_id
    · change ContinuousAt (fun s : ℝ => B.W 0 (realTimeClamp s) w) t
      exact ((B.martingale 0).path P B.F w _ (htime t)).comp real_time_clamp_continuous.continuousAt
  · apply ae_of_all
    intro w t ht htR
    exact (continuousAt_const.add ((hN.path P B.F w _ (htime t)).comp real_time_clamp_continuous.continuousAt)).continuousWithinAt
  · exact he

/-- A bounded price stopped before the terminal time is a genuine M2
martingale, and its gain is the stopped derivative integral. -/
theorem bounded_stopped_harmonic_integral {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (R T : ℝ) (hR : 0≤R) (hRT : R<T)
    (v : (Fin 2 → ℝ) → ℝ) (hv : ContDiffOn ℝ 2 v {q | q 0<T})
    (hpde : ∀ t∈Icc 0 R,∀ x,fderiv ℝ v ![t,x] (Pi.single 0 1)+
      fderiv ℝ (fderiv ℝ v) ![t,x] (Pi.single 1 1) (Pi.single 1 1)/2=0)
    (τ : Ω → Icc (0:ℝ) R)
    (hτ : ∀ t,MeasurableSet[B.F t] {w | realTimeClamp (τ w).val≤t})
    (K : ℝ) (hbound : ∀ᵐ w ∂P,∀ t∈Icc 0 R,
      |v ![min (τ w).val t,B.W 0 (realTimeClamp (min (τ w).val t)) w]|≤K) :
    ∃ N : HalfClosedTime → Ω → ℝ,ContinuousM2Witness P B.F N ∧
      ItoCovarianceFormula P B.F (B.W 0)
        (fun z => (Ioc (⊥ : HalfClosedTime) (realTimeClamp (τ z.1).val)).indicator
          (fun _ => fderiv ℝ v ![(finitePrefixTime (T:=(⊤:EReal)) R hR (realTimeClamp z.2)).val,
            B.W 0 (realTimeClamp z.2) z.1] (Pi.single 1 1)) (realTimeClamp z.2)) N ∧
      ∀ᵐ w ∂P,∀ t∈Icc 0 R,
        v ![min (τ w).val t,B.W 0 (realTimeClamp (min (τ w).val t)) w]=
          v ![0,B.W 0 ⊥ w]+N (realTimeClamp t) w := by
  have htop : (0:EReal)<⊤ := by simp
  obtain ⟨L,hL,hLI,he⟩ := open_harmonic_common_representation P B R T hR hRT v hv hpde
  obtain ⟨hm,hp,hi⟩ := open_price_gradient_regularity P B R T hR hRT v hv
  obtain ⟨c,hc,hcm,hcT,hct,hcut,hcc⟩ := positive_real_time_exhaustion htop
  have hτtop w : realTimeClamp (T:=(⊤:EReal)) (τ w).val<⊤ :=
    real_time_below _ (τ w).property.1 (EReal.coe_lt_top _)
  obtain ⟨Z,hZ,hZI,hZe,_,_⟩ := stopped_brownian_integral_constructed P htop B.F B.mono B.le B.null
    (B.W 0) (B.C 0 0) L (B.martingale 0) (B.cov 0 0) hL c hc hcm hcT hct hcut hcc
    (fun j w r hr => B.diagonal_clock 0 w r hr.1) _ (fun j => hp _ (hc j))
    (fun j => ae_of_all _ fun w => hi _ (hc j) w) hLI (fun w => realTimeClamp (τ w).val) hτtop hτ
  let N := fun t w => L (min (realTimeClamp (τ w).val) t) w
  have hNl := hL.stopped P B.F B.mono B.le (fun w => realTimeClamp (τ w).val) hτ
  have hzero : realTimeClamp (T:=(⊤:EReal)) 0=⊥ := by
    apply Subtype.ext
    simpa using real_time_clamp_eq (T:=(⊤:EReal)) 0 le_rfl le_top
  have hNbound : ∀ᵐ w ∂P,∀ t,‖N t w‖≤2*K := by
    filter_upwards [he,hbound] with w hw hb
    intro t
    obtain ⟨q,hq,hqt,heq⟩ := finite_closed_time_real (min (realTimeClamp (τ w).val) t)
      ((min_le_left _ _).trans_lt (hτtop w))
    have hqτ : q≤(τ w).val := by
      have hle : realTimeClamp (T:=(⊤:EReal)) q≤realTimeClamp (τ w).val := heq ▸ min_le_left _ _
      change (realTimeClamp q:EReal)≤(realTimeClamp (τ w).val:EReal) at hle
      rw [real_time_clamp_eq q hq le_top,real_time_clamp_eq _ (τ w).property.1 le_top] at hle
      exact EReal.coe_le_coe_iff.mp hle
    have hqR := hqτ.trans (τ w).property.2
    have hvq := hb q ⟨hq,hqR⟩
    rw [min_eq_right hqτ] at hvq
    have hv0 := hb 0 ⟨le_rfl,hR⟩
    rw [min_eq_right (τ w).property.1,hzero] at hv0
    have hh := hw q ⟨hq,hqR⟩
    change ‖L (min (realTimeClamp (τ w).val) t) w‖≤2*K
    rw [←heq,Real.norm_eq_abs]
    have hh' : L (realTimeClamp q) w=v ![q,B.W 0 (realTimeClamp q) w]-v ![0,B.W 0 ⊥ w] := by linarith
    rw [hh']
    exact (abs_sub _ _).trans (by linarith)
  have hNM := local_stop_is_m2_of_square_integrable_bound P B.F B.mono B.le L hL
    (fun w => realTimeClamp (τ w).val) hτ hτtop (fun _ => 2*K) (memLp_const _) hNbound
  refine ⟨N,hNM,?_,?_⟩
  · exact hZI.congr_integral P B.F B.mono B.le (B.W 0) Z N _ hZ hNl hZe
  · filter_upwards [he] with w hw
    intro t ht
    simpa only [N,real_time_clamp_mono.map_min] using hw (min (τ w).val t)
      ⟨le_min (τ w).property.1 ht.1,(min_le_right _ _).trans ht.2⟩

end Asakura.Chapter11

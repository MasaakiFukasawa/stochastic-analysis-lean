import Chapter4BrownianVariationIto
import Chapter4BoundedLocalConditional
import Chapter3VariationScalarIntegral

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter5
set_option maxHeartbeats 3600000
set_option backward.isDefEq.respectTransparency false

/-- A harmonic test in the martingale and its own bracket is a martingale
on every interval on which the test is bounded. This allows deterministic
brackets other than time itself. -/
theorem bracket_harmonic_conditional
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (W A : ClosedTime T → Ω → ℝ) (hW : LocalMProcessWitness P F W)
    (hA : LocalCovarianceWitness P F W W A)
    (ψ : (Fin 2 → ℝ) → ℝ) (hψ : ContDiff ℝ 2 ψ)
    (hpde : ∀ x y,fderiv ℝ ψ ![x,y] (Pi.single 1 1)+
      fderiv ℝ (fderiv ℝ ψ) ![x,y] (Pi.single 0 1) (Pi.single 0 1)/2=0)
    (R s : ClosedTime T) (hR : R<⊤) (hs : s≤R) (K : ℝ)
    (hb : ∀ᵐ w ∂P,∀ t,t≤R → |ψ ![W t w,A t w]|≤K) :
    P[(fun w => ψ ![W R w,A R w]) | F s]=ᵐ[P] fun w => ψ ![W s w,A s w] := by
  have hAv := covariance_adapted_variation P F hF hle hW hW hA
  have hAc w t (ht : t<⊤) : ContinuousAt (fun r => A r w) t := by
    have hh := ((hW.path P F w t ht).mul (hW.path P F w t ht)).sub (hA.defect.path P F w t ht)
    convert hh using 1
    funext r
    simp only [Pi.sub_apply,Pi.mul_apply,sub_sub_cancel]
  obtain ⟨c,hc0,hcm,hcT,_,_,hcc⟩ := positive_real_time_exhaustion hT
  let hc := fun n => (hc0 n).le
  obtain ⟨N,D,J,hN,hNI,hD,hJ,he⟩ := martingale_variation_ito P hT F hF hle hnull
    W A A hW hAv hAc hA ψ hψ c hc hcm.monotone hcT hcc
  have hscaled := variation_integral_scalar_multiple P A D _ c hc hD (-2)
  have hJD : VariationIntegralFormula P c hc A
      (fun z => fderiv ℝ (fderiv ℝ ψ) ![W (realTimeClamp z.2) z.1,A (realTimeClamp z.2) z.1]
        (Pi.single 0 1) (Pi.single 0 1)) (fun t w => -2*D t w) := by
    apply variation_integral_integrand_congr_on_domain P A _ _ _ c hc hcT hscaled
    apply ae_of_all
    intro w r _ _
    dsimp only
    linarith [hpde (W (realTimeClamp r) w) (A (realTimeClamp r) w)]
  have heJ := hJ.unique P c hc hcc A J (fun t w => -2*D t w) _ hJD
  have hrep : ∀ᵐ w ∂P,∀ t,t≤R → ψ ![W t w,A t w]=ψ ![W ⊥ w,A ⊥ w]+N t w := by
    filter_upwards [he,heJ] with w hw hjw
    intro t ht
    have hh := hw t (ht.trans_lt hR)
    rw [hjw t (ht.trans_lt hR)] at hh
    linarith
  apply bounded_local_increment_conditional P hT F hF hle _ N hN _ R hR K hb hrep s hs
  intro t ht
  letI : MeasurableSpace Ω := F t
  apply hψ.continuous.measurable.comp
  apply Measurable.of_eval
  intro i
  fin_cases i
  · exact hW.adapted P F t ht
  · exact hAv.adapted t ht

end Asakura.Chapter4

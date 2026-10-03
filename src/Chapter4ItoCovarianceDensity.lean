import Chapter3ContinuousIntegralConstruction
import Chapter3ItoVariationCovariance
import Chapter5TimeDensityVariation
import Chapter5BracketCommonTime
import Chapter4FinitePathLift
import Chapter3OpenPathMeasurable

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter5
set_option maxHeartbeats 3600000
set_option backward.isDefEq.respectTransparency false

/-- Covariance density for an actual Ito integral, including cross
covariances. The density is obtained from the signed variation integral. -/
theorem continuous_ito_covariance_density
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (X Y N C : ClosedTime T → Ω → ℝ)
    (hX : LocalMProcessWitness P F X) (hY : LocalMProcessWitness P F Y)
    (hN : LocalMProcessWitness P F N) (hC : LocalCovarianceWitness P F X N C)
    (H : ClosedTime T → Ω → ℝ)
    (hHa : ∀ t,t<⊤ → Measurable[F t] (H t))
    (hHc : ∀ w t,t<⊤ → ContinuousAt (fun s => H s w) t)
    (hYI : ItoCovarianceFormula P F X (fun z => H (realTimeClamp z.2) z.1) Y)
    (Q : Ω × ℝ → ℝ) (hQm : ∀ w,Measurable (fun r => Q (w,r)))
    (c : ℕ → ℝ) (hc : ∀ n,0≤c n) (hcm : Monotone c) (hcT : ∀ n,(c n:EReal)<T)
    (hcc : ∀ t,t<⊤ → ∃ n,t<realTimeClamp (T := T) (c n))
    (hQi : ∀ n,∀ᵐ w ∂P,IntervalIntegrable (fun r => Q (w,r)) volume 0 (c n))
    (hCQ : ∀ n,∀ᵐ w ∂P,∀ r∈Icc 0 (c n),C (realTimeClamp r) w=∫ s in 0..r,Q (w,s)) :
    ∃ D : ClosedTime T → Ω → ℝ,LocalCovarianceWitness P F Y N D ∧
      (∀ r : ℝ,0≤r → (r:EReal)<T → D (realTimeClamp r)=ᵐ[P]
        fun w => ∫ s in 0..r,H (realTimeClamp s) w*Q (w,s)) ∧
      (∀ n,∀ᵐ w ∂P,∀ r∈Icc 0 (c n),D (realTimeClamp r) w=
        ∫ s in 0..r,H (realTimeClamp s) w*Q (w,s)) := by
  have hCv := covariance_adapted_variation P F hF hle hX hN hC
  have hCc w t (ht : t<⊤) : ContinuousAt (fun s => C s w) t := by
    have hh := ((hX.path P F w t ht).mul (hN.path P F w t ht)).sub (hC.defect.path P F w t ht)
    convert hh using 1
    ext s
    simp only [Pi.sub_apply,Pi.mul_apply,sub_sub_cancel]
  have hreg := open_process_real_regularity F H hHa hHc
  have hHm w := open_path_real_measurable _ (hHc w)
  obtain ⟨I,hIv,hIc,hI⟩ := continuous_adapted_variation_exists P F hF hnull c hc hcm hcT hcc
    C hCv hCc (fun z => H (realTimeClamp z.2) z.1) hreg.1 hreg.2
  obtain ⟨D,hD,he⟩ := ito_covariance_identified_with_variation_integral P hT F X Y N C I
    hY hN hC _ hHm hYI c hc hcT hcc hIc hI
  have hHreal n w : ContinuousOn (fun r => H (realTimeClamp r) w) (Icc 0 (c n)) := by
    intro r hr
    exact ((hHc w _ (real_time_below r hr.1 ((EReal.coe_le_coe hr.2).trans_lt (hcT n)))).comp
      real_time_clamp_continuous.continuousAt).continuousWithinAt
  have hd (r : ℝ) (hr : 0≤r) (hrT : (r:EReal)<T) : D (realTimeClamp r)=ᵐ[P]
      fun w => ∫ s in 0..r,H (realTimeClamp s) w*Q (w,s) := by
    have hi := time_density_variation_integral P C I Q (fun z => H (realTimeClamp z.2) z.1)
      c hc hcT hcc hCQ hQm hQi hHm hHreal hI r hr hrT
    filter_upwards [he,hi] with w hw hiw
    exact (hw _ (real_time_below r hr hrT)).trans hiw
  refine ⟨D,hD,hd,?_⟩
  intro n
  apply bracket_primitive_common_time P (c n) (hc n) (fun r => D (realTimeClamp r))
    (fun w r => H (realTimeClamp r) w*Q (w,r))
  · intro w r hr
    have hrt := real_time_below r hr.1 ((EReal.coe_le_coe hr.2).trans_lt (hcT n))
    have hh := ((hY.path P F w _ hrt).mul (hN.path P F w _ hrt)).sub (hD.defect.path P F w _ hrt)
    have hDc : ContinuousAt (fun t => D t w) (realTimeClamp r) := by
      convert hh using 1
      ext t
      simp only [Pi.sub_apply,Pi.mul_apply,sub_sub_cancel]
    exact (hDc.comp real_time_clamp_continuous.continuousAt).continuousWithinAt
  · filter_upwards [hQi n] with w hw
    exact hw.continuousOn_mul (by simpa only [uIcc_of_le (hc n)] using hHreal n w)
  · intro r hr
    exact hd r hr.1 ((EReal.coe_le_coe hr.2).trans_lt (hcT n))

end Asakura.Chapter4

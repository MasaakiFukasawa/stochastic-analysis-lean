import Chapter12SignedMeasureAddition
import Chapter12ItoReverseAssociativity

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.Chapter12
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

theorem ito_integrator_addition {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t A,MeasurableSet[m] A → P A=0 → MeasurableSet[F t] A)
    (X Z Y V : ClosedTime T → Ω → ℝ) (H : Ω × ℝ → ℝ)
    (hX : LocalMProcessWitness P F X) (hZ : LocalMProcessWitness P F Z)
    (hY : ItoCovarianceFormula P F X H Y) (hV : ItoCovarianceFormula P F Z H V) :
    ItoCovarianceFormula P F (fun t w => X t w+Z t w) H (fun t w => Y t w+V t w) := by
  have hXZ := hX.add P F hF hle hZ
  obtain ⟨J,hJ,hJI⟩ := continuous_adapted_ito_exists P hT F hF hle hnull _ hXZ
    (fun _ => 1) (fun _ _ _ => measurable_const) (fun _ _ _ _ => continuousOn_const)
  intro N C0 hN hC0
  obtain ⟨C,hC⟩ := local_covariance_witness_exists P F hF hle hnull X N hX hN
  obtain ⟨D,hD⟩ := local_covariance_witness_exists P F hF hle hnull Z N hZ hN
  obtain ⟨U,hU,hUp⟩ := hY N C hN hC
  obtain ⟨Q,hQ,hQp⟩ := hV N D hN hD
  obtain ⟨_,_,h0p⟩ := hJI N C0 hN hC0
  have hsum : LocalCovarianceWitness P F (fun t w => X t w+Z t w) N (fun t w => C t w+D t w) := by
    simpa only [one_mul] using hC.bilinear P F hF hle hD 1
  have heC := hsum.unique P F hF hle hC0
  refine ⟨fun t w => U t w+Q t w,?_,?_⟩
  · simpa only [one_mul] using hU.bilinear P F hF hle hQ 1
  intro d hd hdT
  obtain ⟨ν,hν,hν0,hνi,hνU⟩ := hUp d hd hdT
  obtain ⟨κ,hκ,hκ0,hκi,hκQ⟩ := hQp d hd hdT
  obtain ⟨ρ,hρ,hρ0,_,_⟩ := h0p d hd hdT
  have he : ∀ᵐ w ∂P,ρ w=ν w+κ w := by
    filter_upwards [hρ0,hν0,hκ0,heC] with w hr hn hk hew
    have hs : (ν w+κ w).totalVariation (Iic 0)=0 := by
      apply le_antisymm _ bot_le
      calc
        _ ≤ (ν w).totalVariation (Iic 0)+(κ w).totalVariation (Iic 0) := by
          simpa only [SignedMeasure.totalVariation_eq_variation,Measure.add_apply] using
            (VectorMeasure.variation_add_le (μ:=ν w) (ν:=κ w)) (Iic 0)
        _ = 0 := by rw [hn,hk,zero_add]
    apply signed_measure_ext_positive_Ioc _ _ hr hs
    intro a b ha hab
    rw [hρ w a b ha hab,VectorMeasure.add_apply,hν w a b ha hab,hκ w a b ha hab]
    have hbelow s : min (realTimeClamp (T:=T) s) (realTimeClamp d)<⊤ := by
      apply lt_of_le_of_lt (min_le_right _ _)
      change (realTimeClamp d:EReal)<T
      rw [real_time_clamp_eq d hd hdT.le];exact hdT
    rw [←hew _ (hbelow b),←hew _ (hbelow a)]
    ring
  refine ⟨ρ,hρ,hρ0,?_,?_⟩
  · filter_upwards [he,hνi,hκi] with w hw hn hk
    rw [hw]
    exact signed_add_integrable _ _ _ hn hk
  · filter_upwards [he,hνi,hκi,hνU,hκQ] with w hw hn hk hu hq
    rw [hw,signed_integral_add_measure _ _ _ hn hk]
    exact congrArg₂ (·+·) hu hq

end Asakura.Chapter12
#print axioms Asakura.Chapter12.ito_integrator_addition

import Chapter3IdentityItoIntegral
import Chapter2OneSidedStoppedCovariance

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- Stopping the integrator is the actual Ito integral of the deterministic
interval indicator. This is derived from covariance measures. -/
theorem stopped_identity_ito_integral
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t ≤ m)
    (hnull : ∀ t N,MeasurableSet[m] N → P N=0 → MeasurableSet[F t] N)
    (X : ClosedTime T → Ω → ℝ) (hX : LocalMProcessWitness P F X)
    (a : ℝ) (ha : 0≤a) :
    ItoCovarianceFormula P F X
      (fun z => (Ioc 0 a).indicator (fun _ => (1:ℝ)) z.2)
      (fun t w => X (min (realTimeClamp a) t) w) := by
  have hstop : ∀ t,MeasurableSet[F t] {w : Ω | realTimeClamp (T := T) a≤t} := by
    intro t
    by_cases h : realTimeClamp (T := T) a≤t <;> simp [h]
  have hXs := hX.stopped P F hF hle (fun _ => realTimeClamp a) hstop
  intro Y C hY hC
  obtain ⟨D,hD⟩ := local_covariance_witness_exists P F hF hle hnull _ Y hXs hY
  have he := local_covariance_one_sided_stopping P F hF hle hnull X Y C D hX hY hC
    (fun _ => realTimeClamp a) hstop hD
  refine ⟨D,hD,?_⟩
  intro d hd hdT
  obtain ⟨ν,hν,hs⟩ := supported_covariance_measure P F hF hle hnull X Y C hX hY hC d hd hdT
  refine ⟨ν,hν,?_,ae_of_all _ (fun _ => (integrable_const (1:ℝ)).indicator measurableSet_Ioc),?_⟩
  · filter_upwards [hs] with w hw
    have hlo : ∀ᵐ r ∂(ν w).totalVariation,0<r := hw.mono fun _ hr => hr.1
    rw [ae_iff] at hlo
    simpa only [not_lt,Iic] using hlo
  · filter_upwards [he,hX.initial P F,hY.initial P F,hC.defect.initial P F]
      with w hw hx hy hc
    have hzero : C ⊥ w=0 := by
      change X ⊥ w*Y ⊥ w-C ⊥ w=0 at hc
      simp only [hx,hy,Pi.zero_apply,zero_mul,zero_sub] at hc
      linarith
    have hz : realTimeClamp (T := T) 0=⊥ := by
      apply Subtype.ext
      exact real_time_clamp_eq 0 le_rfl (by simpa using hT.le)
    have hdt : realTimeClamp (T := T) d<⊤ := by
      change (realTimeClamp d:EReal)<T
      rw [real_time_clamp_eq d hd hdT.le]
      exact hdT
    rw [hw _ hdt,signedIntegralRaw_indicator _ _ measurableSet_Ioc,hν w 0 a le_rfl ha,
      hz,min_bot_left,hzero,sub_zero]

end Asakura.Chapter5

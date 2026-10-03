import Chapter3SupportedCovarianceMeasure
import Chapter2ItoIntegrandEncoding

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- The unit integrand integrates to the original zero-initial local
martingale, directly from the existing covariance characterization. -/
theorem identity_ito_integral
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X : ClosedTime T → Ω → ℝ) (hX : LocalMProcessWitness P F X) :
    ItoCovarianceFormula P F X (fun _ => 1) X := by
  intro Y C hY hC
  refine ⟨C,hC,?_⟩
  intro d hd hdT
  obtain ⟨ν,hν,hs⟩ := supported_covariance_measure P F hF hle hnull X Y C hX hY hC d hd hdT
  refine ⟨ν,hν,?_,Filter.Eventually.of_forall (fun _ => integrable_const _),?_⟩
  · filter_upwards [hs] with ω hsω
    have hlo : ∀ᵐ r ∂(ν ω).totalVariation, 0 < r := hsω.mono (fun _ h => h.1)
    rw [ae_iff] at hlo
    simpa only [not_lt,Iic] using hlo
  · filter_upwards [hs,hX.initial P F,hY.initial P F,hC.defect.initial P F]
      with ω hsω hx hy hdef
    have hzero : C ⊥ ω = 0 := by
      change X ⊥ ω*Y ⊥ ω-C ⊥ ω = 0 at hdef
      simp only [hx,hy,Pi.zero_apply,zero_mul,zero_sub] at hdef
      linarith
    have hz : realTimeClamp (T := T) 0 = ⊥ := by
      apply Subtype.ext
      exact real_time_clamp_eq 0 le_rfl (by simpa using hT.le)
    have he : signedIntegralRaw (ν ω) (fun _ => 1) =
        signedIntegralRaw (ν ω) ((Ioc 0 d).indicator (fun _ => 1)) := by
      apply signedIntegralRaw_congr_ae (ν ω).totalVariation (ν ω) 1 (by norm_num) (by simp)
      exact hsω.mono (fun r hr => (indicator_of_mem hr (fun _ : ℝ => (1:ℝ))).symm)
    rw [he,signedIntegralRaw_indicator _ _ measurableSet_Ioc,hν ω 0 d le_rfl hd,
      min_self,hz,min_bot_left,hzero,sub_zero]

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.identity_ito_integral

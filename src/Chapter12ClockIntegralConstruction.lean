import Chapter2LocalPositiveIntegral
import Chapter2ContinuousVariationIntegral
import Chapter4ClockVariationIntegral

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.Chapter12
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

theorem clock_integral_constructed {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) {T : EReal} [Fact (0≤T)]
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F)
    (hnull : ∀ t A,MeasurableSet[m] A → P A=0 → MeasurableSet[F t] A)
    (c : ℕ → ℝ) (hc : ∀ n,0≤c n) (hcm : Monotone c) (hcT : ∀ n,(c n:EReal)<T)
    (hcc : ∀ t,t<⊤ → ∃ n,t<realTimeClamp (T:=T) (c n))
    (C : ClosedTime T → Ω → ℝ)
    (hC : ∀ n w r,r∈Icc 0 (c n) → C (realTimeClamp r) w=r)
    (H : Ω × ℝ → ℝ)
    (hH : ∀ n,@Measurable _ _
      (progressiveSpace (fun t : Icc (0:ℝ) (c n) => F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) (c n) => H (z.1,z.2.val)))
    (hi : ∀ n,∀ᵐ w ∂P,Integrable (fun r => H (w,r)) (volume.restrict (Ioc 0 (c n)))) :
    ∃ I : ClosedTime T → Ω → ℝ,AdaptedLocalVariationWitness F I ∧
      (∀ w t,t<⊤ → ContinuousAt (fun s => I s w) t) ∧
      VariationIntegralFormula P c hc C H I := by
  let S n := intervalStieltjes 0 (c n) (hc n) id (monotone_id.monotoneOn _)
    (fun _ _ => continuous_id.continuousWithinAt)
  have hSm n : (S n).measure=volume.restrict (Ioc 0 (c n)) := clock_stieltjes_measure _ _ _
  have hiS n : ∀ᵐ w ∂P,Integrable (fun r => H (w,r)) (S n).measure := by
    rw [hSm];exact hi n
  obtain ⟨I,hI,he⟩ := local_positive_stieltjes_integral_constructed P F hF hnull c hc hcm hcT hcc
    (fun _ => id) (fun _ _ => monotone_id.monotoneOn _)
    (fun _ _ _ _ => continuous_id.continuousWithinAt) (fun _ _ => measurable_const) H hH hiS
  have hIc : ∀ᵐ w ∂P,∀ t,t<⊤ → ContinuousAt (fun s => I s w) t := by
    filter_upwards [he,ae_all_iff.mpr hiS] with w hew hiw
    intro t ht
    obtain ⟨n,hn⟩ := hcc t ht
    have hat : NullSingletonClass (S n).measure := by rw [hSm];infer_instance
    letI := hat
    have hcont := (continuous_cumulative_integral (S n).measure _ (hiw n)).comp
      (continuous_subtype_val.comp (finite_prefix_time_continuous (T:=T) (c n) (hc n)))
    apply hcont.continuousAt.congr_of_eventuallyEq
    filter_upwards [gt_mem_nhds hn] with s hs
    simpa only [Function.comp_def,min_eq_right hs.le] using hew n s
  obtain ⟨J,hJ,hJc,hJI⟩ := local_variation_continuous_representative P F hnull I hI hIc
  refine ⟨J,hJ,hJc,?_⟩
  intro n
  let μ := (S n).measure
  letI : IsFiniteMeasure μ := intervalStieltjes_finite _ _ _ _ _ _
  have htv : μ.toSignedMeasure.totalVariation=μ := by
    rw [SignedMeasure.totalVariation_eq_variation,Measure.variation_toSignedMeasure]
  refine ⟨fun _ => μ.toSignedMeasure,?_,?_,?_,?_⟩
  · simp only [htv]
    exact ae_of_all _ (fun _ => by rw [show μ=volume.restrict (Ioc 0 (c n)) from hSm n];exact ae_restrict_mem measurableSet_Ioc)
  · exact ae_of_all _ (fun w s t hst => by
      rw [Measure.toSignedMeasure_apply_measurable measurableSet_Ioc,
        intervalStieltjes_Ioc_real _ _ _ _ _ _ s t hst,
        hC n w _ (intervalClamp_mem _ _ _ _),hC n w _ (intervalClamp_mem _ _ _ _)];rfl)
  · simpa only [htv] using hiS n
  · filter_upwards [he,hJI,hiS n] with w hew hjw hiw
    intro t
    rw [hjw,hew n t]
    change (∫ r in Iic (finitePrefixTime (c n) (hc n) t).val,H (w,r) ∂μ) =
      signedIntegralRaw μ.toSignedMeasure ((Iic (finitePrefixTime (c n) (hc n) t).val).indicator (fun r => H (w,r)))
    rw [signed_integral_positive_measure μ _ (hiw.indicator measurableSet_Iic),integral_indicator measurableSet_Iic]

end Asakura.Chapter12
#print axioms Asakura.Chapter12.clock_integral_constructed

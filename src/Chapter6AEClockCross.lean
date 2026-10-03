import Chapter2ItoCovarianceCharacterization
import Chapter2SignedMeasureIdentification
import Chapter3PositiveVariationIntegral
import Chapter4BrownianTimeMeasure
import Chapter7ClockHalfTime

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter6
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false

/-- Cross bracket identification for a merely measurable Ito integrand,
when the original bracket is either clock time or zero. This covers all
pairs of Brownian coordinates, without continuity of the coefficient. -/
theorem ae_measurable_ito_clock_cross
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (F : HalfClosedTime → MeasurableSpace Ω)
    (W V N C : HalfClosedTime → Ω → ℝ)
    (hV : LocalMProcessWitness P F V) (hN : LocalMProcessWitness P F N)
    (hC : LocalCovarianceWitness P F W V C)
    (H : Ω × ℝ → ℝ) (hNI : ItoCovarianceFormula P F W H N)
    (diag : Prop) [Decidable diag]
    (hclock : ∀ w (r : ℝ),0 ≤ r → C (realTimeClamp r) w = if diag then r else 0)
    (hi : ∀ b : ℝ,0≤b → ∀ᵐ w ∂P,IntervalIntegrable (fun r => H (w,r)) volume 0 b) :
    ∃ D,LocalCovarianceWitness P F N V D ∧ ∀ b : ℝ,0 ≤ b →
      D (realTimeClamp b) =ᵐ[P] fun w => if diag then ∫ r in 0..b,H (w,r) else 0 := by
  obtain ⟨D,hD,hd⟩ := hNI V C hV hC
  refine ⟨D,hD,?_⟩
  intro b hb
  obtain ⟨ν,hν,hν0,_,hνD⟩ := hd b hb (EReal.coe_lt_top b)
  filter_upwards [hν0,hνD,hi b hb] with w hn0 he hiw
  rw [he]
  by_cases hdg : diag
  · let μ := (intervalStieltjes 0 b hb id (monotone_id.monotoneOn _)
      (fun _ _ => continuous_id.continuousWithinAt)).measure
    letI : IsFiniteMeasure μ := intervalStieltjes_finite _ _ _ _ _ _
    have hμ : μ = volume.restrict (Ioc 0 b) := clock_stieltjes_measure 0 b hb
    have heν : ν w = μ.toSignedMeasure := by
      apply signed_measure_ext_positive_Ioc _ _ hn0
      · rw [SignedMeasure.totalVariation_eq_variation,Measure.variation_toSignedMeasure,hμ,
          Measure.restrict_apply measurableSet_Iic]
        have he0 : Iic (0:ℝ) ∩ Ioc 0 b = ∅ := by ext x; simp; grind
        rw [he0,measure_empty]
      · intro s t hs hst
        rw [hν w s t hs hst,← real_time_clamp_mono.map_min,← real_time_clamp_mono.map_min,
          hclock w _ (le_min (hs.trans hst) hb),hclock w _ (le_min hs hb),if_pos hdg,
          Measure.toSignedMeasure_apply_measurable measurableSet_Ioc,
          intervalStieltjes_Ioc_real 0 b hb id (monotone_id.monotoneOn _) (fun _ _ => continuous_id.continuousWithinAt) s t hst]
        simp only [if_pos hdg,id_eq,intervalClamp,Set.coe_projIcc,max_eq_right (le_min hb (hs.trans hst)),max_eq_right (le_min hb hs),min_comm]
    rw [heν,signed_integral_positive_measure μ _ (by rw [hμ]; exact hiw.1),if_pos hdg]
    exact clock_stieltjes_integral 0 b hb _
  · have heν : ν w = 0 := by
      apply signed_measure_ext_positive_Ioc _ _ hn0
      · simp [SignedMeasure.totalVariation_eq_variation]
      · intro s t hs hst
        rw [hν w s t hs hst,← real_time_clamp_mono.map_min,← real_time_clamp_mono.map_min,
          hclock w _ (le_min (hs.trans hst) hb),hclock w _ (le_min hs hb)]
        simp only [if_neg hdg,sub_self,VectorMeasure.zero_apply]
    rw [heν,if_neg hdg]
    simpa using signed_integral_positive_measure (0 : Measure ℝ) (fun r => H (w,r)) integrable_zero_measure

end Asakura.Chapter6

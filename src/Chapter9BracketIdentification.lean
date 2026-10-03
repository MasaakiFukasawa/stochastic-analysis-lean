import Chapter2LocalCovarianceAE
import Chapter2LocalCovarianceRules
import Chapter2CommonTimeEquality

open MeasureTheory Set Filter
namespace Asakura.Chapter9
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- Product-test and Ito product identities identify the bracket: their
 difference is both a local martingale and a finite-variation process. -/
theorem bracket_from_product_identity {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t,F t≤m)
    (M N C D Q I J : ClosedTime T → Ω → ℝ)
    (hM : LocalMProcessWitness P F M) (hN : LocalMProcessWitness P F N)
    (hC : LocalCovarianceWitness P F M N C)
    (hD : LocalVariationWitness F D)
    (hDm : ∀ t,Measurable[F t] (D t)) (hDc : ∀ w,Continuous (fun t => D t w))
    (hQ : LocalMProcessWitness P F Q)
    (hI : LocalMProcessWitness P F I) (hJ : LocalMProcessWitness P F J)
    (he : ∀ᵐ w ∂P,∀ t,t<⊤ → Q t w-I t w-J t w=C t w-D t w) :
    LocalCovarianceWitness P F M N D := by
  have hL := ((hQ.add P F hF hle (hI.smul P F (-1))).add P F hF hle (hJ.smul P F (-1)))
  have hCD : LocalMProcessWitness P F (fun t w => C t w-D t w) := by
    apply hL.congr_ae_of_stopped_regular P F
    · filter_upwards [he] with w hw
      intro t ht
      simpa only [neg_one_mul,← sub_eq_add_neg] using hw t ht
    · intro σ hσ hσt
      obtain ⟨hcm,hcc⟩ := hC.stopped_regular P F hF hle hM hN σ hσ hσt
      have hdm := stopped_min_value_measurable F hF σ hσ D hDm
        (fun w t => (hDc w).continuousAt.continuousWithinAt)
      exact ⟨fun t => (hcm t).sub (hdm t),fun w =>
        (hcc w).sub ((hDc w).comp (continuous_const.min continuous_id))⟩
  have hv := hC.variation.add F (hD.smul F (-1))
  obtain ⟨τ,hτ,hmono,_,hco,hparts⟩ := hv.localizers
  have hh n w : ∃ U V : ClosedTime T → ℝ,Monotone U ∧ Monotone V ∧
      ∀ t,C (min (τ n w) t) w-D (min (τ n w) t) w=U t-V t := by
    simpa only [neg_one_mul,← sub_eq_add_neg] using hparts n w
  have hz := local_finite_variation_intersection_zero P F hF hle _ hCD τ hτ hmono hco hh
  refine ⟨hC.defect.congr_ae_of_stopped_regular P F ?_ ?_,hD⟩
  · filter_upwards [hz] with w hw
    intro t ht
    have heq := hw t ht
    change M t w*N t w-C t w=M t w*N t w-D t w
    linarith
  · intro σ hσ hσt
    obtain ⟨hmm,hmc⟩ := hM.stopped_regular P F hF hle σ hσ hσt
    obtain ⟨hnm,hnc⟩ := hN.stopped_regular P F hF hle σ hσ hσt
    have hdm := stopped_min_value_measurable F hF σ hσ D hDm
      (fun w t => (hDc w).continuousAt.continuousWithinAt)
    exact ⟨fun t => ((hmm t).mul (hnm t)).sub (hdm t),fun w =>
      ((hmc w).mul (hnc w)).sub ((hDc w).comp (continuous_const.min continuous_id))⟩
theorem bracket_from_product_identity_pointwise {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T) (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t,F t≤m)
    (M N C D Q I J : ClosedTime T → Ω → ℝ)
    (hM : LocalMProcessWitness P F M) (hN : LocalMProcessWitness P F N)
    (hC : LocalCovarianceWitness P F M N C)
    (hD : LocalVariationWitness F D)
    (hDm : ∀ t,Measurable[F t] (D t)) (hDc : ∀ w,Continuous (fun t => D t w))
    (hQ : LocalMProcessWitness P F Q)
    (hI : LocalMProcessWitness P F I) (hJ : LocalMProcessWitness P F J)
    (he : ∀ t,t<⊤ → (fun w => Q t w-I t w-J t w)=ᵐ[P] (fun w => C t w-D t w)) :
    LocalCovarianceWitness P F M N D := by
  letI : Nonempty (Iio (⊤ : ClosedTime T)) := ⟨⟨⊥,hT⟩⟩
  have hc := continuous_process_common_time_equality P
    (fun t : Iio (⊤ : ClosedTime T) => fun w => Q t.val w-I t.val w-J t.val w)
    (fun t : Iio (⊤ : ClosedTime T) => fun w => C t.val w-D t.val w)
    (fun w => by
      apply continuous_iff_continuousAt.mpr
      intro t
      exact (((hQ.path P F w t.val t.property).sub (hI.path P F w t.val t.property)).sub
        (hJ.path P F w t.val t.property)).comp continuous_subtype_val.continuousAt)
    (fun w => (hC.continuous_open_paths P F M N C hM hN w).sub
      ((hDc w).comp continuous_subtype_val)) (fun t => he t.val t.property)
  exact bracket_from_product_identity P F hF hle M N C D Q I J hM hN hC hD hDm hDc hQ hI hJ
    (hc.mono (fun w hw t ht => hw ⟨t,ht⟩))

end Asakura.Chapter9

import Chapter7ClosedConstantExtension
import Chapter7MonotoneClosedExtension
import Chapter3IncreasingAdaptedVariation
import Chapter3OpenProcessRegularity

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete
set_option maxHeartbeats 3500000
set_option backward.isDefEq.respectTransparency false

/-- Extension of the actual quadratic variation across a finite endpoint.
The increasing representative is constructed on an ambient null set, so
pathwise monotonicity is not an added hypothesis. -/
theorem closed_covariance_constant_extension
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (R : ℝ) [Fact (0 ≤ (R:EReal))] (hR : 0 < (R:EReal))
    (F : ClosedTime (R:EReal) → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t,F t ≤ m)
    (hnull : ∀ t N,MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X C : ClosedTime (R:EReal) → Ω → ℝ)
    (hX : LocalMProcessWitness P F X) (hC : LocalCovarianceWitness P F X X C)
    (ha : ∀ t,Measurable[F t] (X t)) (hc : ∀ w,Continuous (fun t => X t w))
    (hCa : ∀ t,Measurable[F t] (C t)) (hCc : ∀ w,Continuous (fun t => C t w)) :
    ∃ D : HalfClosedTime → Ω → ℝ,
      LocalCovarianceWitness P (fun t => F (closedPrefixProjection R t))
        (fun t w => X (closedPrefixProjection R t) w) (fun t w => X (closedPrefixProjection R t) w) D ∧
      (∀ᵐ w ∂P,∀ t,D t w = C (closedPrefixProjection R t) w) := by
  classical
  have hm : ∀ᵐ w ∂P,Monotone (fun t => C t w) :=
    (local_quadratic_variation_monotone P F hF hle hnull X C hX hC).mono
      (fun w hw => monotone_at_continuous_endpoint hR _ (hCc w) hw)
  let N := toMeasurable P {w | ¬Monotone (fun t => C t w)}
  have hN : P N = 0 := by rw [measure_toMeasurable]; simpa only [ae_iff] using hm
  have hNm t : MeasurableSet[F t] N := hnull t N (measurableSet_toMeasurable _ _) hN
  have hn : ∀ᵐ w ∂P,w ∉ N := by simpa only [ae_iff,not_not,Set.setOf_mem_eq] using hN
  let A := fun t w => if w ∈ N then 0 else C t w
  have hAm t : Measurable[F t] (A t) := Measurable.ite (hNm t) measurable_const (hCa t)
  have hAc w : Continuous (fun t => A t w) := by
    by_cases hw : w ∈ N <;> simp only [A,hw,ite_true,ite_false]
    · exact continuous_const
    · exact hCc w
  have hAo w : Monotone (fun t => A t w) := by
    by_cases hw : w ∈ N
    · simpa only [A,if_pos hw] using (monotone_const : Monotone (fun _ : ClosedTime (R:EReal) => (0:ℝ)))
    · have hg : Monotone (fun t => C t w) := not_not.mp (fun hh => hw (subset_toMeasurable P _ hh))
      simpa only [A,if_neg hw] using hg
  have hL : LocalMProcessWitness P F (fun t w => X t w*X t w-A t w) := by
    apply Asakura.Chapter3Complete.LocalMProcessWitness.congr_ae_open P F hF hC.defect
      (fun t _ => ((ha t).mul (ha t)).sub (hAm t))
      (fun w t _ => ((hc w).mul (hc w)).continuousAt.sub (hAc w).continuousAt)
    exact hn.mono fun w hw t _ => by simp only [Pi.sub_apply,Pi.mul_apply,A,if_neg hw]
  let p := closedPrefixProjection R
  let D := fun t w => A (p t) w
  have hd := closed_local_constant_extension P R F hF hle _ hL
    (fun t => ((ha t).mul (ha t)).sub (hAm t)) (fun w => ((hc w).mul (hc w)).sub (hAc w))
  have hv := continuous_increasing_adapted_variation (by simp : (0:EReal) < ⊤)
    (fun t => F (p t)) (hF.comp (closed_prefix_projection_mono R)) D
    (fun t _ => hAm _) (fun w => ((hAo w).comp (closed_prefix_projection_mono R)).monotoneOn (Iio ⊤))
    (fun w t _ => ((hAc w).comp (closed_prefix_projection_continuous R)).continuousAt)
  exact ⟨D,⟨hd,hv.toPathwise⟩,hn.mono fun w hw t => by simp only [D,A,p,if_neg hw]⟩

end Asakura.Chapter7

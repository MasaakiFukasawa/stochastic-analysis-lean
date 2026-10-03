import Chapter7LocalFlatPaths
import Chapter3IncreasingAdaptedVariation
import Chapter2LocalNullModification

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false

/-- Choose simultaneous representatives without strengthening DDS to
pointwise assumptions. On the exceptional null set use X=0 and one fixed
good clock path, so the replacement clock remains divergent everywhere. -/
theorem dds_regular_representatives
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t ≤ m)
    (hnull : ∀ t N,MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X C : ClosedTime T → Ω → ℝ) (hX : LocalMProcessWitness P F X)
    (hC : LocalCovarianceWitness P F X X C)
    (hdiv : ∀ᵐ w ∂P,∀ r : ℝ,∃ t,t < ⊤ ∧ r < C t w) :
    ∃ Y A : ClosedTime T → Ω → ℝ,
      LocalMProcessWitness P F Y ∧ LocalCovarianceWitness P F Y Y A ∧
      (∀ᵐ w ∂P,∀ t,Y t w = X t w ∧ A t w = C t w) ∧
      (∀ w,MonotoneOn (fun t => A t w) (Iio ⊤)) ∧
      (∀ w t,t < ⊤ → ContinuousAt (fun s => A s w) t) ∧
      (∀ w,Y ⊥ w = 0 ∧ A ⊥ w = 0) ∧
      (∀ w r,∃ t,t < ⊤ ∧ r < A t w) ∧
      (∀ w a b,a < ⊤ → b < ⊤ → A a w = A b w → Y a w = Y b w) := by
  classical
  let good := fun w => MonotoneOn (fun t => C t w) (Iio ⊤) ∧
    X ⊥ w = 0 ∧ C ⊥ w = 0 ∧
    (∀ r : ℝ,∃ t,t < ⊤ ∧ r < C t w) ∧
    (∀ a b,a < ⊤ → b < ⊤ → C a w = C b w → X a w = X b w)
  have hg : ∀ᵐ w ∂P,good w := by
    filter_upwards [local_quadratic_variation_monotone P F hF hle hnull X C hX hC,
      hX.initial P F,local_quadratic_variation_initial P F X C hX hC,hdiv,
      local_martingale_constant_on_bracket_levels P hT F hF hle hnull X C hX hC]
      with w hm hx hc hd hf
    exact ⟨hm,hx,hc,hd,hf⟩
  let N := toMeasurable P {w | ¬good w}
  have hN : P N = 0 := by rw [measure_toMeasurable]; simpa only [ae_iff] using hg
  have hNm t : MeasurableSet[F t] N := hnull t N (measurableSet_toMeasurable _ _) hN
  have hn : ∀ᵐ w ∂P,w ∉ N := by simpa only [ae_iff,not_not,Set.setOf_mem_eq] using hN
  have hgood (w) (hw : w ∉ N) : good w :=
    not_not.mp (fun hh => hw (subset_toMeasurable P {w | ¬good w} hh))
  obtain ⟨w0,hw0⟩ := hn.exists
  have hg0 := hgood w0 hw0
  let Y := fun t w => if w ∈ N then 0 else X t w
  let A := fun t w => if w ∈ N then C t w0 else C t w
  have hY : LocalMProcessWitness P F Y := local_martingale_null_modification P F N hNm hN X hX
  have hCc := local_covariance_path_continuous P F X X C hX hX hC
  have hAm t (ht : t < ⊤) : Measurable[F t] (A t) :=
    Measurable.ite (hNm t) measurable_const (hC.adapted P F hX hX t ht)
  have hAc w t (ht : t < ⊤) : ContinuousAt (fun s => A s w) t := by
    by_cases hw : w ∈ N
    · simpa only [A,if_pos hw] using hCc w0 t ht
    · simpa only [A,if_neg hw] using hCc w t ht
  have hAo w : MonotoneOn (fun t => A t w) (Iio ⊤) := by
    by_cases hw : w ∈ N
    · simpa only [A,if_pos hw] using hg0.1
    · simpa only [A,if_neg hw] using (hgood w hw).1
  have hA : LocalCovarianceWitness P F Y Y A := by
    refine ⟨?_,(continuous_increasing_adapted_variation hT F hF A hAm hAo hAc).toPathwise⟩
    apply Asakura.Chapter3Complete.LocalMProcessWitness.congr_ae_open P F hF hC.defect
    · intro t ht
      exact ((hY.adapted P F t ht).mul (hY.adapted P F t ht)).sub (hAm t ht)
    · intro w t ht
      exact ((hY.path P F w t ht).mul (hY.path P F w t ht)).sub (hAc w t ht)
    · filter_upwards [hn] with w hw
      intro t ht
      simp only [Y,A,if_neg hw]
  refine ⟨Y,A,hY,hA,hn.mono (fun w hw t => by simp [Y,A,hw]),hAo,hAc,?_,?_,?_⟩
  · intro w
    by_cases hw : w ∈ N
    · simp only [Y,A,if_pos hw,hg0.2.2.1,and_self]
    · simpa only [Y,A,if_neg hw] using ⟨(hgood w hw).2.1,(hgood w hw).2.2.1⟩
  · intro w r
    by_cases hw : w ∈ N
    · simpa only [A,if_pos hw] using hg0.2.2.2.1 r
    · simpa only [A,if_neg hw] using (hgood w hw).2.2.2.1 r
  · intro w a b ha hb he
    by_cases hw : w ∈ N
    · simp only [Y,if_pos hw]
    · simp only [A,if_neg hw] at he
      simpa only [Y,if_neg hw] using (hgood w hw).2.2.2.2 a b ha hb he

end Asakura.Chapter7

import Chapter3OpenProcessRegularity
import Chapter3UnweightedCovariationApproximation
import Chapter3CommonOscillationPartition
import Chapter2LocalQuadraticVariation

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter6
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false

/-- Once a process is a semimartingale under both equivalent measures,
its quadratic variations agree. A single oscillation partition is constructed
for both decompositions; the two actual pathwise limits are then compared. -/
theorem semimartingale_quadratic_variation_invariant
    {Ω : Type*} {m : MeasurableSpace Ω}
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t ≤ m)
    (hnullP : ∀ t E,MeasurableSet[m] E → P E = 0 → MeasurableSet[F t] E)
    (hnullQ : ∀ t E,MeasurableSet[m] E → Q E = 0 → MeasurableSet[F t] E)
    (hAE : ∀ p : Ω → Prop,(∀ᵐ w ∂P,p w) ↔ ∀ᵐ w ∂Q,p w)
    (X A M B N C D : ClosedTime T → Ω → ℝ)
    (hXP : SemimartingaleDecomposition P F X A M)
    (hXQ : SemimartingaleDecomposition Q F X B N)
    (hC : LocalCovarianceWitness P F M M C)
    (hD : LocalCovarianceWitness Q F N N D) :
    ∀ᵐ w ∂P,∀ t,t < ⊤ → C t w = D t w := by
  let V : Fin 4 → ClosedTime T → Ω → ℝ := ![A,M,B,N]
  have ha i t (ht : t < ⊤) : Measurable[F t] (V i t) := by
    fin_cases i
    · exact hXP.variation.adapted t ht
    · exact hXP.martingale.adapted P F t ht
    · exact hXQ.variation.adapted t ht
    · exact hXQ.martingale.adapted Q F t ht
  have hc i w t (ht : t < ⊤) : ContinuousAt (fun s => V i s w) t := by
    fin_cases i
    · exact hXP.variation_continuous P F w t ht
    · exact hXP.martingale.path P F w t ht
    · exact hXQ.variation_continuous Q F w t ht
    · exact hXQ.martingale.path Q F w t ht
  obtain ⟨u,hu,_,huT,hum,hut,huc⟩ := positive_real_time_exhaustion hT
  obtain ⟨τ,h0,hs,hm,ht,hco,hb,hLP⟩ := common_oscillation_partition P F hF hle V ha hc
    (fun n => realTimeClamp (u n)) hum.monotone hut huc
  have hLQ i n j t : eLpNorm (fun w =>
      V i (min (τ n (j+1) w) t) w-V i (min (τ n j w) t) w) ∞ Q ≤ ENNReal.ofReal ((1/2:ℝ)^n) := by
    have hsm k := (open_process_stopped_regular F hF (V i) (ha i) (hc i) (τ n k) (hs n k) (ht n k)).1 t
    have hmeas : Measurable (fun w => V i (min (τ n (j+1) w) t) w-V i (min (τ n j w) t) w) :=
      ((hsm (j+1)).sub (hsm j)).mono (hle t) le_rfl
    simpa using eLpNorm_le_of_ae_bound (p := ∞) hmeas.aestronglyMeasurable
      (.of_forall (fun w => hb i n j w t))
  letI : Nonempty (Iio (⊤ : ClosedTime T)) := ⟨⟨⊥,hT⟩⟩
  let q := TopologicalSpace.denseSeq (Iio (⊤ : ClosedTime T))
  have hq := TopologicalSpace.denseRange_denseSeq (Iio (⊤ : ClosedTime T))
  have hp n := unweighted_semimartingale_covariation_approximation P hT F hF hle hnullP
    X X A A M M C hXP hXP hC τ hs hm ht h0 hco q hq
    (fun k j i => hLP 1 k j (q i).val) (fun k j i => hLP 1 k j (q i).val)
    (fun k j i => hLP 0 k j (q i).val) (fun k j i => hLP 0 k j (q i).val)
    (u n) (hu n).le (huT n)
  have hq' n := unweighted_semimartingale_covariation_approximation Q hT F hF hle hnullQ
    X X B B N N D hXQ hXQ hD τ hs hm ht h0 hco q hq
    (fun k j i => hLQ 3 k j (q i).val) (fun k j i => hLQ 3 k j (q i).val)
    (fun k j i => hLQ 2 k j (q i).val) (fun k j i => hLQ 2 k j (q i).val)
    (u n) (hu n).le (huT n)
  have hzC := local_quadratic_variation_initial P F M C hXP.martingale hC
  have hzD := (hAE _).mpr (local_quadratic_variation_initial Q F N D hXQ.martingale hD)
  filter_upwards [ae_all_iff.mpr hp,(hAE _).mpr (ae_all_iff.mpr hq'),hzC,hzD] with w hp hq hc hd
  intro t ht
  obtain ⟨n,hn⟩ := huc t ht
  have he := tendsto_nhds_unique ((hp n).tendsto_at t) ((hq n).tendsto_at t)
  simpa only [min_eq_right hn.le,hc,hd,Pi.zero_apply,sub_zero] using he

end Asakura.Chapter6

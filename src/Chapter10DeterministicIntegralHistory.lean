import Chapter10DeterministicOscillationPartition
import Chapter10CompletedLimitMeasurability
import Chapter3SemimartingaleIntegralApproximation

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter10
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

/-- A deterministic continuous coefficient integral is measurable from the
completed history of its integrator. The proof uses the actual integral's
proved discrete approximation, not a separate definition of the integral. -/
theorem deterministic_integral_history_measurable {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : HalfClosedTime → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (X A M Z : HalfClosedTime → Ω → ℝ) (hX : SemimartingaleDecomposition P F X A M)
    (H : HalfClosedTime → ℝ) (hH : ∀ t,t<⊤ → ContinuousAt H t)
    (c : ℕ → ℝ) (hc : ∀ k,0≤c k) (hcT : ∀ k,(c k:EReal)<⊤)
    (hcc : ∀ t : HalfClosedTime,t<⊤ → ∃ k,t<realTimeClamp (c k))
    (hZ : SemimartingaleIntegralFormula P F c hc A M (fun z => H (realTimeClamp z.2)) Z)
    (b : HalfClosedTime) (hb : b<⊤)
    (G : MeasurableSpace Ω) (hG : G≤m)
    (hGn : ∀ E,MeasurableSet[m] E → P E=0 → MeasurableSet[G] E)
    (hXG : ∀ s,s≤b → Measurable[G] (X s)) : Measurable[G] (Z b) := by
  letI : MeasurableSpace Ω := m
  obtain ⟨τ,h0,hm,ht,hco,hbound⟩ := deterministic_oscillation_partitions H hH
  have hs : ∀ n j t,MeasurableSet[F t] {w : Ω | τ n j≤t} := by
    intro n j t
    by_cases h : τ n j≤t <;> simp [h]
  letI : Nonempty (Iio (⊤ : HalfClosedTime)) := ⟨⟨⊥,by change (0:EReal)<⊤; simp⟩⟩
  let q := TopologicalSpace.denseSeq (Iio (⊤ : HalfClosedTime))
  have hap := semimartingale_integral_approximation P (by simp : (0:EReal)<⊤) F hF hle hnull
    X A M (fun t _ => H t) Z hX (fun _ _ => measurable_const) (fun _ t ht => hH t ht)
    c hc hcT hcc hZ (fun n j _ => τ n j) hs (fun n _ => hm n) (fun n j _ => ht n j)
    (fun n _ => h0 n) (fun n _ t ht => hco n t ht) q (TopologicalSpace.denseRange_denseSeq _)
    (by
      intro n j i
      simpa using eLpNorm_le_of_ae_bound (μ := P) (p := ∞) aestronglyMeasurable_const
        (ae_of_all _ fun _ => hbound n j (q i).val)) b hb
  let Y := fun n w => ∑' j,H (τ n j)*(X (min (τ n (j+1)) b) w-X (min (τ n j) b) w)
  have hYm n : Measurable[G] (Y n) := by
    letI : MeasurableSpace Ω := G
    apply Measurable.tsum
    intro j
    exact measurable_const.mul ((hXG _ (min_le_right _ _)).sub (hXG _ (min_le_right _ _)))
  have hl : ∀ᵐ w ∂P,Tendsto (fun n => Y n w) atTop (𝓝 (Z b w)) := by
    filter_upwards [hap] with w hw
    simpa only [Y,min_self] using hw.tendsto_at b
  obtain ⟨I,J,hZD,_,_⟩ := hZ
  have hZm : Measurable[m] (Z b) := by
    have he := funext (hZD.decomposition b hb)
    rw [he]
    exact ((hZD.variation.adapted b hb).add (hZD.martingale.adapted P F b hb)).mono (hle b) le_rfl
  exact completed_ae_limit_measurable P G hG hGn Y (Z b) hYm hZm hl

end Asakura.Chapter10

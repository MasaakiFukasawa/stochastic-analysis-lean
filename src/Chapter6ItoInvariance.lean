import Chapter3OpenProcessRegularity
import Chapter3SemimartingaleIntegralApproximation
import Chapter3CommonOscillationPartition

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter6
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false

/-- The same stopping sums converge to both Ito integrals under equivalent
measures. The common partition and both limiting identities are constructed. -/
theorem semimartingale_ito_integral_invariant
    {Ω : Type*} {m : MeasurableSpace Ω}
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t ≤ m)
    (hnullP : ∀ t E,MeasurableSet[m] E → P E = 0 → MeasurableSet[F t] E)
    (hnullQ : ∀ t E,MeasurableSet[m] E → Q E = 0 → MeasurableSet[F t] E)
    (hAE : ∀ p : Ω → Prop,(∀ᵐ w ∂P,p w) ↔ ∀ᵐ w ∂Q,p w)
    (X A M B N H I J : ClosedTime T → Ω → ℝ)
    (hXP : SemimartingaleDecomposition P F X A M)
    (hXQ : SemimartingaleDecomposition Q F X B N)
    (hHa : ∀ t,t < ⊤ → Measurable[F t] (H t))
    (hHc : ∀ w t,t < ⊤ → ContinuousAt (fun s => H s w) t)
    (c : ℕ → ℝ) (hc : ∀ n,0 ≤ c n) (hcT : ∀ n,(c n:EReal) < T)
    (hcc : ∀ t,t < ⊤ → ∃ n,t < realTimeClamp (T := T) (c n))
    (hI : SemimartingaleIntegralFormula P F c hc A M (fun z => H (realTimeClamp z.2) z.1) I)
    (hJ : SemimartingaleIntegralFormula Q F c hc B N (fun z => H (realTimeClamp z.2) z.1) J) :
    ∀ᵐ w ∂P,∀ t,t < ⊤ → I t w = J t w := by
  obtain ⟨u,_,_,_,hum,hut,huc⟩ := positive_real_time_exhaustion hT
  obtain ⟨τ,h0,hs,hm,ht,hco,hb,hLP⟩ := common_oscillation_partition P F hF hle
    (fun _ : Unit => H) (fun _ => hHa) (fun _ => hHc)
    (fun n => realTimeClamp (u n)) hum.monotone hut huc
  have hLQ n j t : eLpNorm (fun w =>
      H (min (τ n (j+1) w) t) w-H (min (τ n j w) t) w) ∞ Q ≤ ENNReal.ofReal ((1/2:ℝ)^n) := by
    have hsm k := (open_process_stopped_regular F hF H hHa hHc (τ n k) (hs n k) (ht n k)).1 t
    have hmeas : Measurable (fun w => H (min (τ n (j+1) w) t) w-H (min (τ n j w) t) w) :=
      ((hsm (j+1)).sub (hsm j)).mono (hle t) le_rfl
    simpa using eLpNorm_le_of_ae_bound (p := ∞) hmeas.aestronglyMeasurable
      (.of_forall (fun w => hb () n j w t))
  letI : Nonempty (Iio (⊤ : ClosedTime T)) := ⟨⟨⊥,hT⟩⟩
  let q := TopologicalSpace.denseSeq (Iio (⊤ : ClosedTime T))
  have hq := TopologicalSpace.denseRange_denseSeq (Iio (⊤ : ClosedTime T))
  have hp n := semimartingale_integral_approximation P hT F hF hle hnullP X A M H I hXP hHa hHc
    c hc hcT hcc hI τ hs hm ht h0 hco q hq (fun k j i => hLP () k j (q i).val)
    (realTimeClamp (u n)) (hut n)
  have hq' n := semimartingale_integral_approximation Q hT F hF hle hnullQ X B N H J hXQ hHa hHc
    c hc hcT hcc hJ τ hs hm ht h0 hco q hq (fun k j i => hLQ k j (q i).val)
    (realTimeClamp (u n)) (hut n)
  filter_upwards [ae_all_iff.mpr hp,(hAE _).mpr (ae_all_iff.mpr hq')] with w hp hq
  intro t ht
  obtain ⟨n,hn⟩ := huc t ht
  have he := tendsto_nhds_unique ((hp n).tendsto_at t) ((hq n).tendsto_at t)
  simpa only [min_eq_right hn.le] using he

end Asakura.Chapter6

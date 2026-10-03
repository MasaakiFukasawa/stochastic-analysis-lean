import Chapter3IncreasingWeightProduct
import Chapter3RegularizedWeightRegularity

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

/-- Construct the Ito integral against an increasing nonnegative weight and prove its bound. -/
theorem increasing_ito_weight_constructed
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X V : ClosedTime T → Ω → ℝ) (hX : LocalMProcessWitness P F X)
    (hVa : ∀ t, t < ⊤ → Measurable[F t] (V t))
    (hVc : ∀ ω t, t < ⊤ → ContinuousAt (fun s => V s ω) t)
    (hVm : ∀ ω, MonotoneOn (fun t => V t ω) (Iio ⊤))
    (hVp : ∀ ω t, t < ⊤ → 0 ≤ V t ω) :
    ∃ Y : ClosedTime T → Ω → ℝ,
      LocalMProcessWitness P F Y ∧
      ItoCovarianceFormula P F X (fun z => V (realTimeClamp z.2) z.1) Y ∧
      (∀ᵐ ω ∂P, ∀ t, t < ⊤ → ∀ K : ℝ, 0 ≤ K →
        (∀ s, s ≤ t → |X s ω| ≤ K) → |Y t ω| ≤ 2*K*V t ω) := by
  have hVr := open_process_real_regularity F V hVa hVc
  obtain ⟨Y,hY,hy⟩ := continuous_adapted_ito_exists P hT F hF hle hnull X hX
    (fun z => V (realTimeClamp z.2) z.1) hVr.1 hVr.2
  have hVv := continuous_increasing_adapted_variation hT F hF V hVa hVm hVc
  have hXr := open_process_real_regularity F X (hX.adapted P F) (hX.path P F)
  obtain ⟨c,hc,hcm,hcT,_,_,hcc⟩ := positive_real_time_exhaustion hT
  obtain ⟨I,_,_,hI⟩ := continuous_adapted_variation_exists P F hF hnull c (fun n => (hc n).le)
    hcm.monotone hcT hcc V hVv hVc (fun z => X (realTimeClamp z.2) z.1) hXr.1 hXr.2
  have hb := increasing_weight_ito_bound P hT F hF hle hnull X V Y I hX hVv hVm hVc hVp hY hy
    c (fun n => (hc n).le) hcT hcc hI
  exact ⟨Y,hY,hy,hb.mono (fun _ h => h.2)⟩

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.increasing_ito_weight_constructed

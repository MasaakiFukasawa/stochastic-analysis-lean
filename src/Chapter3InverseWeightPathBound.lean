import Chapter3InverseItoWeights
import Chapter3IncreasingWeightProduct
import Chapter3RegularizedWeightRegularity

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

/-- Construct inverse-weight integrals and derive the path bound from actual
Stieltjes integration by parts. Neither associativity nor the path bound is a hypothesis. -/
theorem inverse_increasing_weight_path_bound
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X G V : ClosedTime T → Ω → ℝ) (hX : LocalMProcessWitness P F X)
    (hGa : ∀ t, t < ⊤ → Measurable[F t] (G t))
    (hGc : ∀ ω t, t < ⊤ → ContinuousAt (fun s => G s ω) t)
    (hVa : ∀ t, t < ⊤ → Measurable[F t] (V t))
    (hVc : ∀ ω t, t < ⊤ → ContinuousAt (fun s => V s ω) t)
    (hVm : ∀ ω, MonotoneOn (fun t => V t ω) (Iio ⊤))
    (hVp : ∀ ω t, t < ⊤ → 0 ≤ V t ω)
    (hprod : ∀ ω t, t < ⊤ → V t ω*G t ω = 1) :
    ∃ Y : ClosedTime T → Ω → ℝ,
      LocalMProcessWitness P F Y ∧
      ItoCovarianceFormula P F X (fun z => G (realTimeClamp z.2) z.1) Y ∧
      (∀ᵐ ω ∂P, ∀ t, t < ⊤ → ∀ K : ℝ, 0 ≤ K →
        (∀ s, s ≤ t → |Y s ω| ≤ K) →
        ∀ s, s ≤ t → |X s ω| ≤ 2*K*V t ω) := by
  have hGr := open_process_real_regularity F G hGa hGc
  have hVr := open_process_real_regularity F V hVa hVc
  obtain ⟨Y,Z,hY,hZ,hy,hz,he⟩ := continuous_inverse_ito_weights_constructed P hT F hF hle hnull
    X hX (fun z => G (realTimeClamp z.2) z.1) (fun z => V (realTimeClamp z.2) z.1)
    hGr.1 hVr.1 hGr.2 hVr.2 (by
      intro ω r hr hrT
      apply hprod
      change (realTimeClamp r : EReal) < T
      rw [real_time_clamp_eq r hr hrT.le]
      exact hrT)
  have hVv := continuous_increasing_adapted_variation hT F hF V hVa hVm hVc
  have hYr := open_process_real_regularity F Y (hY.adapted P F) (hY.path P F)
  obtain ⟨c,hc,hcm,hcT,_,_,hcc⟩ := positive_real_time_exhaustion hT
  obtain ⟨I,_,_,hI⟩ := continuous_adapted_variation_exists P F hF hnull c (fun n => (hc n).le)
    hcm.monotone hcT hcc V hVv hVc (fun z => Y (realTimeClamp z.2) z.1) hYr.1 hYr.2
  have hbound := increasing_weight_ito_bound P hT F hF hle hnull Y V Z I hY hVv hVm hVc hVp hZ hz
    c (fun n => (hc n).le) hcT hcc hI
  refine ⟨Y,hY,hy,?_⟩
  filter_upwards [he,hbound] with ω heω hbω
  intro t ht K hK hYK s hst
  have hs : s < ⊤ := hst.trans_lt ht
  rw [← heω s hs]
  exact (hbω.2 s hs K hK (fun u hus => hYK u (hus.trans hst))).trans
    (mul_le_mul_of_nonneg_left (hVm ω hs ht hst) (by positivity))

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.inverse_increasing_weight_path_bound

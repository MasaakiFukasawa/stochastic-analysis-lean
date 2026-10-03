import Chapter9ContinuousDriftVariation
import Chapter4FiniteCovarianceSum
import Chapter2SemimartingaleDecomposition

open MeasureTheory Set
open scoped BigOperators
namespace Asakura.Chapter10
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter9
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

/-- Turn the constructed finite-horizon linear SDE into the actual
semimartingale decomposition used by the proved Ito product formula. -/
theorem finite_sde_decomposition {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : HalfClosedTime → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    {n : ℕ} (N : Fin n → HalfClosedTime → Ω → ℝ)
    (hN : ∀ j,LocalMProcessWitness P F (N j))
    (X a : ℝ → Ω → ℝ) (ξ : Ω → ℝ) (hξ : Measurable[F ⊥] ξ)
    (T : ℝ) (hT : 0≤T)
    (hX : ∀ w,ContinuousOn (fun r => X r w) (Icc 0 T))
    (ha : ∀ r∈Icc 0 T,Measurable[F (realTimeClamp r)] (a r))
    (hac : ∀ w,ContinuousOn (fun r => a r w) (Icc 0 T))
    (he : ∀ w r,r∈Icc 0 T → X r w=ξ w+(∫ s in 0..r,a s w)+∑ j,N j (realTimeClamp r) w) :
    SemimartingaleDecomposition P F
      (fun t w => X (finitePrefixTime T hT t).val w)
      (fun t w => ξ w+∫ r in 0..(finitePrefixTime T hT t).val,a r w)
      (fun t w => ∑ j,N j (min (realTimeClamp T) t) w) := by
  have hsum := local_martingale_finset_sum P (by simp : (0:EReal)<⊤) F hF hle
    Finset.univ N (fun j _ => hN j)
  have hstop : ∀ t,MeasurableSet[F t] {w : Ω | realTimeClamp (T := ⊤) T≤t} := by
    intro t
    by_cases h : realTimeClamp (T := ⊤) T≤t <;> simp [h]
  refine ⟨continuous_drift_variation F hF a ξ hξ T hT ha hac,
    hsum.stopped P F hF hle (fun _ => realTimeClamp T) hstop,?_,?_⟩
  · intro w t _
    exact ((hX w).comp_continuous
      (continuous_subtype_val.comp (finite_prefix_time_continuous T hT))
      (fun s => (finitePrefixTime T hT s).property)).continuousAt
  · intro t _ w
    rw [he w _ (finitePrefixTime T hT t).property,finite_prefix_time_clamp T hT le_top]

end Asakura.Chapter10

import Chapter10DeterministicIntegralHistory
import Chapter10LinearReconstructionMeasurable
import Chapter8BrownianForcingPath

open MeasureTheory Set Filter
open scoped BigOperators
namespace Asakura.Chapter10
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter8
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

/-- Matrix coefficient integrals are measurable as continuous paths in the
completed information of their integrator, proved entry by entry from the
actual semimartingale integral formulas. -/
theorem vector_integral_history_measurable {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d r : ℕ}
    (F : HalfClosedTime → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (X A M : Fin r → HalfClosedTime → Ω → ℝ)
    (hX : ∀ j,SemimartingaleDecomposition P F (X j) (A j) (M j))
    (H : Fin d → Fin r → HalfClosedTime → ℝ)
    (hH : ∀ i j t,t<⊤ → ContinuousAt (H i j) t)
    (c : ℕ → ℝ) (hc : ∀ k,0≤c k) (hcT : ∀ k,(c k:EReal)<⊤)
    (hcc : ∀ t : HalfClosedTime,t<⊤ → ∃ k,t<realTimeClamp (c k))
    (N : Fin d → Fin r → HalfClosedTime → Ω → ℝ)
    (hN : ∀ i j,SemimartingaleIntegralFormula P F c hc (A j) (M j)
      (fun z => H i j (realTimeClamp z.2)) (N i j))
    (T : ℝ) (hT : 0≤T) (Z : Ω → C(Icc (0:ℝ) T,Fin d → ℝ))
    (hZ : ∀ w t i,Z w t i=∑ j,N i j (realTimeClamp t.val) w)
    (G : MeasurableSpace Ω) (hG : G≤m)
    (hGn : ∀ E,MeasurableSet[m] E → P E=0 → MeasurableSet[G] E)
    (hXG : ∀ j s,s≤realTimeClamp T → Measurable[G] (X j s)) :
    Measurable[G] Z := by
  letI : MeasurableSpace Ω := G
  apply ContinuousMap.measurable_iff_eval.mpr
  intro t
  apply Measurable.of_eval
  intro i
  have he : (fun w => Z w t i)=(fun w => ∑ j,N i j (realTimeClamp t.val) w) :=
    funext (fun w => hZ w t i)
  rw [he]
  apply Finset.measurable_sum
  intro j _
  exact deterministic_integral_history_measurable (m := m) P F hF hle hnull
    (X j) (A j) (M j) (N i j) (hX j) (H i j) (hH i j) c hc hcT hcc
    (hN i j) (realTimeClamp t.val) (half_real_time_finite _) G hG hGn
    (fun s hs => hXG j s (hs.trans (real_time_clamp_mono t.property.2)))

end Asakura.Chapter10

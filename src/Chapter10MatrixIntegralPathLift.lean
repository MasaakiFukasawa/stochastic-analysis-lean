import Chapter10MatrixIntegralPath
import Chapter10DeterministicIntegralStopped
import Chapter2LocalPositiveIntegral

open MeasureTheory Set Filter
open scoped BigOperators
namespace Asakura.Chapter10
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter8
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

/-- Lift the finite continuous integral path back to the half-line. The entry
integrals are proved constant after the finite endpoint, so the two
representations agree at every finite time on one common probability-one set. -/
theorem matrix_integral_path_lift {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d r : ℕ}
    (F : HalfClosedTime → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (T : ℝ) (hT : 0≤T) (Y : Ω → C(Icc (0:ℝ) T,Fin r → ℝ))
    (A M : Fin r → HalfClosedTime → Ω → ℝ)
    (hY : ∀ j,SemimartingaleDecomposition P F (fun t w => Y w (finitePrefixTime T hT t) j) (A j) (M j))
    (H : Fin d → Fin r → HalfClosedTime → ℝ)
    (hH : ∀ i j t,t<⊤ → ContinuousAt (H i j) t)
    (c : ℕ → ℝ) (hc : ∀ k,0≤c k) (hcT : ∀ k,(c k:EReal)<⊤)
    (hcc : ∀ t : HalfClosedTime,t<⊤ → ∃ k,t<realTimeClamp (c k))
    (N : Fin d → Fin r → HalfClosedTime → Ω → ℝ)
    (hN : ∀ i j,SemimartingaleIntegralFormula P F c hc (A j) (M j)
      (fun z => H i j (realTimeClamp z.2)) (N i j))
    (Z : Ω → C(Icc (0:ℝ) T,Fin d → ℝ))
    (hZ : ∀ w t i,Z w t i=∑ j,N i j (realTimeClamp t.val) w) :
    ∀ᵐ w ∂P,∀ t,t<⊤ → ∀ i,Z w (finitePrefixTime T hT t) i=∑ j,N i j t w := by
  have hs i j := deterministic_integral_stopped_integrator P F hF hle hnull
    (fun t w => Y w (finitePrefixTime T hT t) j) (A j) (M j) (N i j) (hY j)
    (H i j) (hH i j) (realTimeClamp T) (by
      intro w t
      have hh := finite_prefix_time_stop (T := (⊤:EReal)) T T hT le_rfl le_top t
      rw [show finitePrefixTime T hT (min (realTimeClamp T) t)=finitePrefixTime T hT t from Subtype.ext hh])
    c hc hcT hcc (hN i j)
  filter_upwards [ae_all_iff.mpr (fun i => ae_all_iff.mpr (hs i))] with w hw
  intro t ht i
  rw [hZ,finite_prefix_time_clamp T hT le_top]
  simp_rw [←hw i _ t ht]

end Asakura.Chapter10

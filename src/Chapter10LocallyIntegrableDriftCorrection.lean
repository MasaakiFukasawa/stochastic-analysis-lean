import Chapter10LocallyIntegrableDrift
import Chapter8BrownianForcingPath

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter10
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter8
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

/-- Subtracting the predicted drift before stochastic integration equals
subtracting its ordinary weighted time integral afterwards. All three
stochastic integrals here have the manuscript's actual integral formulas. -/
theorem observation_locally_integrable_drift_correction {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : HalfClosedTime → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (X Y B A D M N U V Z : HalfClosedTime → Ω → ℝ)
    (hX : SemimartingaleDecomposition P F X A M)
    (hY : SemimartingaleDecomposition P F Y D N)
    (hB : SemimartingaleDecomposition P F B B (fun _ _ => 0))
    (hYX : ∀ w t,t<⊤ → Y t w=X t w+B t w)
    (b : ℝ → Ω → ℝ) (hbm : ∀ w,Measurable (fun t => b t w))
    (hbi : ∀ w a d,IntervalIntegrable (fun t => b t w) volume a d)
    (hBint : ∀ w t,0≤t → B (realTimeClamp t) w=∫ s in 0..t,b s w)
    (H : HalfClosedTime → ℝ) (hH : ∀ t,t<⊤ → ContinuousAt H t)
    (c : ℕ → ℝ) (hc : ∀ k,0≤c k) (hcT : ∀ k,(c k:EReal)<⊤)
    (hcc : ∀ t : HalfClosedTime,t<⊤ → ∃ k,t<realTimeClamp (c k))
    (hU : SemimartingaleIntegralFormula P F c hc A M (fun z => H (realTimeClamp z.2)) U)
    (hV : SemimartingaleIntegralFormula P F c hc B (fun _ _ => 0) (fun z => H (realTimeClamp z.2)) V)
    (hZ : SemimartingaleIntegralFormula P F c hc D N (fun z => H (realTimeClamp z.2)) Z) :
    ∀ᵐ w ∂P,∀ t,0≤t → U (realTimeClamp t) w=
      Z (realTimeClamp t) w-∫ s in 0..t,H (realTimeClamp s)*b s w := by
  have hHr : Continuous (fun s : ℝ => H (realTimeClamp s)) := by
    apply continuous_iff_continuousAt.mpr
    intro s
    exact (hH _ (half_real_time_finite s)).comp real_time_clamp_continuous.continuousAt
  have hv := observation_locally_integrable_drift_integral P F hF hle hnull B V b _ hbm hbi hHr hBint c hc hcT hcc hV
  have hlin := finite_deterministic_integral_linearity (ι := Bool) P F hF hle hnull
    (fun j => if j then B else X) (fun j => if j then B else A)
    (fun j => if j then (fun _ _ => 0) else M) (fun j => if j then V else U)
    Y D N Z (fun j => by cases j <;> assumption) hY (fun _ => H) H (fun _ => hH) hH
    c hc hcT hcc (fun j => by cases j <;> assumption) hZ (by
      intro w s t hs ht
      rw [hYX w s hs,hYX w t ht]
      simp [Fintype.sum_bool]
      ring)
  filter_upwards [hv,hlin] with w hv hl
  intro t ht
  have hh := hl _ (half_real_time_finite t)
  simp [Fintype.sum_bool] at hh
  rw [hv t ht] at hh
  linarith

end Asakura.Chapter10

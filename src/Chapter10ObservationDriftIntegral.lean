import Chapter10FiniteIntegralLinearity
import Chapter5TimeDensityInitial
import Chapter5ZeroIto
import Chapter8BrownianForcingPath

open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal
namespace Asakura.Chapter10
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter8
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

/-- The actual stochastic integral against a continuous drift primitive
is its ordinary time integral, simultaneously at every nonnegative time. -/
theorem observation_drift_integral {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : HalfClosedTime → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (B Z : HalfClosedTime → Ω → ℝ) (b : ℝ → Ω → ℝ) (H : ℝ → ℝ)
    (hb : ∀ w,Continuous (fun t => b t w)) (hH : Continuous H)
    (hB : ∀ w t,0≤t → B (realTimeClamp t) w=∫ s in 0..t,b s w)
    (c : ℕ → ℝ) (hc : ∀ k,0≤c k) (hcT : ∀ k,(c k:EReal)<⊤)
    (hcc : ∀ t : HalfClosedTime,t<⊤ → ∃ k,t<realTimeClamp (c k))
    (hZ : SemimartingaleIntegralFormula P F c hc B (fun _ _ => 0) (fun z => H z.2) Z) :
    ∀ᵐ w ∂P,∀ t,0≤t → Z (realTimeClamp t) w=∫ s in 0..t,H s*b s w := by
  obtain ⟨I,N,hZ,hI,hN⟩ := hZ
  have hn := integral_against_zero_martingale P (by simp : (0:EReal)<⊤)
    F hF hle hnull N (fun z => H z.2) hZ.martingale hN
  have he t (ht : 0≤t) : Z (realTimeClamp t)=ᵐ[P] (fun w => ∫ s in 0..t,H s*b s w) := by
    have hi := time_density_variation_integral_with_initial P B I (fun _ => 0) (fun z => b z.2 z.1)
      (fun z => H z.2) c hc hcT hcc
      (fun n => ae_of_all _ fun w r hr => by simpa only [zero_add] using hB w r hr.1)
      (fun w => (hb w).measurable) (fun n => ae_of_all _ fun w => (hb w).intervalIntegrable _ _)
      (fun _ => hH.measurable) (fun _ _ => hH.continuousOn) hI t ht (EReal.coe_lt_top t)
    filter_upwards [hi,hn] with w hi hn
    rw [hZ.decomposition _ (real_time_below t ht (EReal.coe_lt_top t)) w,
      hn _ (real_time_below t ht (EReal.coe_lt_top t)),add_zero]
    exact hi
  have hall := continuous_process_common_time_equality P
    (fun t : ℝ≥0 => Z (realTimeClamp t.val)) (fun t : ℝ≥0 => fun w => ∫ s in 0..t.val,H s*b s w)
    (fun w => by
      have hr : Continuous (fun s : ℝ => Z (realTimeClamp s) w) :=
        continuous_iff_continuousAt.mpr fun s =>
          (hZ.continuous w _ (half_real_time_finite s)).comp real_time_clamp_continuous.continuousAt
      exact hr.comp continuous_subtype_val)
    (fun w => by
      have hh := hH.mul (hb w)
      have hi : Continuous (fun t : ℝ => ∫ s in 0..t,H s*b s w) :=
        continuous_iff_continuousAt.mpr fun t =>
          (intervalIntegral.integral_hasDerivAt_right (hh.intervalIntegrable 0 t)
            (hh.stronglyMeasurableAtFilter _ _) hh.continuousAt).continuousAt
      exact hi.comp continuous_subtype_val)
    (fun t => he t.val t.property)
  filter_upwards [hall] with w hw
  intro t ht
  exact hw ⟨t,ht⟩

end Asakura.Chapter10

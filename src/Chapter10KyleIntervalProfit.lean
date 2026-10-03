import Chapter10KyleItoIdentity
import Mathlib.Tactic.LinearCombination
open MeasureTheory Set Filter
namespace Asakura.Chapter10
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter8
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

/-- Derive the remaining-interval profit formula from the actual Ito identity. -/
theorem kyle_ito_interval_profit_identity {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : HalfClosedTime → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t Q,MeasurableSet[m] Q → P Q=0 → MeasurableSet[F t] Q)
    (B C E A : HalfClosedTime → Ω → ℝ) (V : Ω → ℝ) (p0 l σ : ℝ) (hl : 0<l)
    (α : Ω × ℝ → ℝ) (hαm : ∀ w,Measurable (fun s => α (w,s)))
    (hαi : ∀ t,0≤t → ∀ w,IntervalIntegrable (fun s => α (w,s)) volume 0 t)
    (hB : LocalMProcessWitness P F B) (hC : LocalCovarianceWitness P F B B C)
    (hclock : ∀ t,0≤t → ∀ w,C (realTimeClamp t) w=t)
    (hE : SemimartingaleDecomposition P F E A (fun t w => (-l*σ)*B t w))
    (hA : ∀ t,0≤t → ∀ w,A (realTimeClamp t) w=V w-p0-l*(∫ s in 0..t,α (w,s))) :
    ∃ Z : HalfClosedTime → Ω → ℝ,LocalMProcessWitness P F Z ∧
      ItoCovarianceFormula P F B (fun z => E (realTimeClamp z.2) z.1) Z ∧
      ∀ s t : ℝ,0≤s → s≤t → ∀ᵐ w ∂P,
        (∫ u in s..t,E (realTimeClamp u) w*α (w,u))=
          ((E (realTimeClamp s) w)^2-(E (realTimeClamp t) w)^2)/(2*l)+l*σ^2*(t-s)/2-
            σ*(Z (realTimeClamp t) w-Z (realTimeClamp s) w) := by
  obtain ⟨Z,hZ,hZI,hp⟩ := kyle_ito_profit_identity P F hF hle hnull B C E A V p0 l σ hl
    α hαm hαi hB hC hclock hE hA
  refine ⟨Z,hZ,hZI,?_⟩
  intro s t hs hst
  filter_upwards [hp s hs,hp t (hs.trans hst)] with w hpS hpT
  have hEr : Continuous (fun u : ℝ => E (realTimeClamp u) w) := by
    apply continuous_iff_continuousAt.mpr
    intro u
    exact (hE.continuous w _ (half_real_time_finite u)).comp real_time_clamp_continuous.continuousAt
  have hIs := (hαi s hs w).continuousOn_mul hEr.continuousOn
  have hIt := (hαi t (hs.trans hst) w).continuousOn_mul hEr.continuousOn
  have hadd := intervalIntegral.integral_add_adjacent_intervals hIs (hIs.symm.trans hIt)
  linear_combination hpT-hpS+hadd

end Asakura.Chapter10

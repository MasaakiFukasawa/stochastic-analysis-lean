import Chapter6ProgressiveClockCross
import Chapter5CumulativeStieltjesIntegral

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter6
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false

/-- The covariance-density calculation does not require continuous
integrands: local integrability of the density and its product suffices. -/
theorem measurable_ito_covariance_density
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (F : HalfClosedTime → MeasurableSpace Ω)
    (W V N C : HalfClosedTime → Ω → ℝ)
    (hV : LocalMProcessWitness P F V) (hC : LocalCovarianceWitness P F W V C)
    (H G : Ω × ℝ → ℝ)
    (hH : ∀ w,Measurable (fun r => H (w,r))) (hG : ∀ w,Measurable (fun r => G (w,r)))
    (hNI : ItoCovarianceFormula P F W H N)
    (hi : ∀ b : ℝ,0 ≤ b → ∀ᵐ w ∂P,IntervalIntegrable (fun r => G (w,r)) volume 0 b)
    (hprod : ∀ b : ℝ,0 ≤ b → ∀ᵐ w ∂P,IntervalIntegrable (fun r => H (w,r)*G (w,r)) volume 0 b)
    (hclock : ∀ b : ℝ,0 ≤ b → ∀ᵐ w ∂P,∀ r ∈ Icc 0 b,
      C (realTimeClamp r) w = ∫ s in 0..r,G (w,s)) :
    ∃ D,LocalCovarianceWitness P F N V D ∧ ∀ b : ℝ,0 ≤ b →
      D (realTimeClamp b) =ᵐ[P] fun w => ∫ r in 0..b,H (w,r)*G (w,r) := by
  obtain ⟨D,hD,hd⟩ := hNI V C hV hC
  refine ⟨D,hD,?_⟩
  intro b hb
  obtain ⟨ν,hν,hν0,hνi,hνD⟩ := hd b hb (EReal.coe_lt_top b)
  filter_upwards [hν0,hνi,hνD,hi b hb,hprod b hb,hclock b hb] with w hn0 hni he hgi hpi hci
  rw [he]
  apply cumulative_stieltjes_density_integral b hb _ _ (hG w) (hH w) hgi (ν w) hni hpi
  intro s t hst
  rw [signed_measure_Ioc_clip_zero (ν w) hn0,
    hν w (max 0 s) (max 0 t) (le_max_left _ _) (max_le_max_left _ hst),
    ← real_time_clamp_mono.map_min,← real_time_clamp_mono.map_min,
    hci _ ⟨le_min (le_max_left _ _) hb,min_le_right _ _⟩,
    hci _ ⟨le_min (le_max_left _ _) hb,min_le_right _ _⟩]
  have hcl (r : ℝ) : min (max 0 r) b = intervalClamp 0 b hb r := by
    change min (max 0 r) b = max 0 (min b r)
    grind
  rw [hcl t,hcl s]

end Asakura.Chapter6

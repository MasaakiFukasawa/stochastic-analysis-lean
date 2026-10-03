import Chapter5ItoRepresentationActual

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- A represented terminal variable supplies the continuous conditional
expectation process used by the frozen BSDE construction. -/
theorem conditional_process_from_represented_terminal
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (F : ClosedTime T → MeasurableSpace Ω) (hle : ∀ t,F t≤m)
    (U : Ω → ℝ) (hU : MemLp U 2 P) (M : ClosedTime T → Ω → ℝ)
    (hM : ContinuousM2Witness P F M) (c : ℝ)
    (hrep : U =ᵐ[P] fun w => c+M ⊤ w) :
    Measurable (fun z : Ω × ℝ => c+M (realTimeClamp z.2) z.1) ∧
      (∀ w,Continuous (fun r : ℝ => c+M (realTimeClamp r) w)) ∧
      (∀ t,Measurable[F t] (fun w => c+M t w)) ∧
      (∀ t,(fun w => c+M t w) =ᵐ[P] P[U|F t]) := by
  have hc : ∀ w,Continuous (fun r : ℝ => c+M (realTimeClamp r) w) :=
    fun w => continuous_const.add ((hM.path w).comp real_time_clamp_continuous)
  have hm t : Measurable[F t] (fun w => c+M t w) := measurable_const.add (hM.adapted t)
  have hj : Measurable (fun z : Ω × ℝ => c+M (realTimeClamp z.2) z.1) :=
    (measurable_uncurry_of_continuous_of_measurable hc (fun r => (hm (realTimeClamp r)).mono (hle _) le_rfl)).comp measurable_swap
  refine ⟨hj,hc,hm,?_⟩
  intro t
  have he := condExp_congr_ae (m := F t) hrep
  have ha := condExp_add (integrable_const c) ((hM.moment ⊤).integrable (by norm_num)) (F t)
  rw [condExp_of_stronglyMeasurable (hle t) stronglyMeasurable_const (integrable_const c)] at ha
  filter_upwards [he,ha,hM.martingale t ⊤ le_top] with w hew haw hmw
  simp only [Pi.add_apply,hmw] at haw
  exact (hew.trans haw).symm

end Asakura.Chapter5

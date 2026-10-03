import Chapter6ContinuousCoefficientMeasurable

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter6
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter7
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

/-- Constant extension of a finite-horizon coefficient is progressive
on every finite interval; it adds no assumption to the original data. -/
theorem finite_coefficient_extension_progressive {Ω : Type*} {m : MeasurableSpace Ω}
    (F : HalfClosedTime → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (H : ℝ → Ω → ℝ) (R : ℝ) (hR : 0≤R)
    (ha : ∀ r∈Icc 0 R,Measurable[F (realTimeClamp r)] (H r))
    (hc : ∀ w,ContinuousOn (fun r => H r w) (Icc 0 R)) :
    let G := fun z : Ω × ℝ => finiteDriftExtension H R z.2 z.1
    Measurable G ∧ (∀ b,0<b → @Measurable _ _
      (progressiveSpace (fun t : Icc (0:ℝ) b => F (realTimeClamp t.val))) inferInstance
        (fun z : Ω × Icc (0:ℝ) b => G (z.1,z.2.val))) := by
  let G := fun z : Ω × ℝ => finiteDriftExtension H R z.2 z.1
  have he := finite_drift_extension H R hR hc
  refine ⟨(finite_coefficient_regularity F hF hle H R hR ha hc).1,?_⟩
  intro b hb
  apply continuous_adapted_real_progressive F hF G b hb.le _ (fun w => (he.1 w).continuousOn)
  intro r hr
  have ht : max 0 (min R r)≤r := max_le hr.1 (min_le_right R r)
  exact (ha _ ⟨le_max_left _ _,max_le hR (min_le_left R r)⟩).mono
    (hF (real_time_clamp_mono ht)) le_rfl

end Asakura.Chapter6

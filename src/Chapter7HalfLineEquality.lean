import Chapter7ClockHalfTime
import Chapter2RightContinuousCommonEquality

open MeasureTheory Set Filter
open scoped Topology NNReal
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete

/-- Deterministic-time equalities between continuous half-line processes
hold on one common event, without claiming a value at infinity. -/
theorem half_line_common_equality
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X Y : HalfClosedTime → Ω → ℝ)
    (hX : ∀ w t,t < ⊤ → ContinuousAt (fun s => X s w) t)
    (hY : ∀ w t,t < ⊤ → ContinuousAt (fun s => Y s w) t)
    (he : ∀ r : ℝ,0 ≤ r → X (realTimeClamp r) =ᵐ[P] Y (realTimeClamp r)) :
    ∀ᵐ w ∂P,∀ t,t < ⊤ → X t w = Y t w := by
  have hh (n : ℕ) : ∀ᵐ w ∂P,∀ r ∈ Icc (0:ℝ) (n+1:ℝ),X (realTimeClamp r) w = Y (realTimeClamp r) w := by
    apply right_continuous_common_equality P (n+1:ℝ) (by positivity)
      (fun r => X (realTimeClamp r)) (fun r => Y (realTimeClamp r))
    · exact .of_forall (fun w r hr _ => ((hX w _ (changed_time_finite r hr)).comp
        real_time_clamp_continuous.continuousAt).continuousWithinAt)
    · exact .of_forall (fun w r hr _ => ((hY w _ (changed_time_finite r hr)).comp
        real_time_clamp_continuous.continuousAt).continuousWithinAt)
    · exact fun r hr => he r hr.1
  filter_upwards [ae_all_iff.mpr hh] with w hw
  intro t ht
  obtain ⟨r,hr,_,rfl⟩ := finite_closed_time_real t ht
  obtain ⟨n,hn⟩ := exists_nat_gt r
  exact hw n r ⟨hr,hn.le.trans (by linarith)⟩

end Asakura.Chapter7

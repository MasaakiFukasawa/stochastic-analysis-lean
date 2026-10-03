import Chapter4VectorCoefficientEnergy
import Chapter4VectorFiniteLift
import Chapter5ProgressivePrimitive

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter4.Vector
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter5
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false

/-- Construct each coordinate's ordinary time integral as an adapted
continuous random path, with its L² bound deduced from coefficient energy. -/
theorem drift_path_constructed
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] {dim : ℕ}
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (R : ℝ) (hR : 0≤R)
    (Y : Ω → C(Icc (0:ℝ) R,Fin dim → ℝ)) (hm : Measurable[m] Y)
    (ha : ∀ r,Measurable[F (realTimeClamp r.val)] (fun w => Y w r))
    (b : (Fin dim → ℝ) → ℝ) (hb : Continuous b)
    (hi : MemLp (fun z : Ω × ℝ => b (Y z.1 (projIcc 0 R hR z.2))) 2
      (P.prod (volume.restrict (Ioc (0:ℝ) R)))) :
    ∃ D : Ω → C(Icc (0:ℝ) R,ℝ),Measurable[m] D ∧ MemLp D 2 P ∧
      (∀ r,Measurable[F (realTimeClamp r.val)] (fun w => D w r)) ∧
      (∀ w r,D w r=∫ s in 0..r.val,b (Y w (projIcc 0 R hR s))) ∧
      (∫ w,‖D w‖^2 ∂P)≤R*(∫ s in 0..R,(∫ w,b (Y w (projIcc 0 R hR s))^2 ∂P)) := by
  letI : MeasurableSpace Ω := m
  let H := fun z : Ω × ℝ => b (Y z.1 (projIcc 0 R hR z.2))
  have hH w : Continuous (fun r => H (w,r)) := hb.comp ((Y w).continuous.comp continuous_projIcc)
  let D : Ω → C(Icc (0:ℝ) R,ℝ) := fun w =>
    ⟨fun r => ∫ s in 0..r.val,H (w,s),
      (intervalIntegral.differentiable_integral_of_continuous (hH w)).continuous.comp continuous_subtype_val⟩
  have hHp := continuous_adapted_real_progressive F hF H R hR
    (by intro r hr; simpa only [Function.comp_def,H,projIcc_of_mem hR hr] using hb.measurable.comp (ha ⟨r,hr⟩))
    (fun w => (hH w).continuousOn)
  have hDa r : Measurable[F (realTimeClamp r.val)] (fun w => D w r) :=
    progressive_time_primitive_adapted R hR (fun r => F (realTimeClamp r.val)) H hHp r
  have hDm : Measurable[m] D := ContinuousMap.measurable_iff_eval.mpr (fun r => (hDa r).mono (hle _) le_rfl)
  have hHm : Measurable[m.prod inferInstance] H := hb.measurable.comp (clamped_path_evaluation_measurable R hR Y hm)
  obtain ⟨hDi,hDb⟩ := Asakura.Chapter4.drift_path_moment_bound P R hR H hHm hi D hDm.aestronglyMeasurable
    (.of_forall (fun w r => rfl))
  exact ⟨D,hDm,hDi,hDa,fun _ _ => rfl,hDb⟩

end Asakura.Chapter4.Vector

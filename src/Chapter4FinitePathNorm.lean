import Chapter4BrownianItoMaximal
import FullAuditPathSpaceExercise

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option backward.isDefEq.respectTransparency false

/-- Restrict a continuous stopped path to the ordinary real interval.
This connects the Chapter 2 time type to the path norm used in Chapter 4. -/
noncomputable def finiteRealPath
    {Ω : Type*} {T : EReal} [Fact (0 ≤ T)]
    (Z : ClosedTime T → Ω → ℝ) (d : ℝ)
    (hc : ∀ ω, Continuous (fun t => Z (min (realTimeClamp d) t) ω))
    (ω : Ω) : C(Icc (0:ℝ) d,ℝ) :=
  ⟨fun r => Z (realTimeClamp r.val) ω,
    by
      have h : Continuous (fun r : Icc (0:ℝ) d => Z (min (realTimeClamp d) (realTimeClamp r.val)) ω) :=
        (hc ω).comp (real_time_clamp_continuous.comp continuous_subtype_val)
      convert h using 1
      funext r
      rw [min_eq_right (real_time_clamp_mono r.property.2)]⟩

theorem finite_real_path_norm_le
    {Ω : Type*} {T : EReal} [Fact (0 ≤ T)]
    (Z : ClosedTime T → Ω → ℝ) (d : ℝ)
    (hc : ∀ ω, Continuous (fun t => Z (min (realTimeClamp d) t) ω)) (ω : Ω) :
    ‖finiteRealPath Z d hc ω‖ ≤ ‖continuousPath (fun t ω => Z (min (realTimeClamp d) t) ω) hc ω‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).2
  intro r
  have h := ContinuousMap.norm_coe_le_norm
    (continuousPath (fun t ω => Z (min (realTimeClamp d) t) ω) hc ω) (realTimeClamp r.val)
  simpa only [finiteRealPath,ContinuousMap.coe_mk,continuousPath,
    min_eq_right (real_time_clamp_mono r.property.2)] using h

theorem finite_real_path_measurable
    {Ω : Type*} {m : MeasurableSpace Ω} {T : EReal} [Fact (0 ≤ T)]
    (F : ClosedTime T → MeasurableSpace Ω) (hle : ∀ t, F t ≤ m)
    (Z : ClosedTime T → Ω → ℝ) (d : ℝ) (hdT : (d:EReal) < T)
    (hc : ∀ ω, Continuous (fun t => Z (min (realTimeClamp d) t) ω))
    (hZ : ∀ t, t < ⊤ → Measurable[F t] (Z t)) :
    Measurable[m] (finiteRealPath Z d hc) := by
  apply ContinuousMap.measurable_iff_eval.mpr
  intro r
  apply (hZ _ ?_).mono (hle _) le_rfl
  change (realTimeClamp r.val : EReal) < T
  rw [real_time_clamp_eq r.val r.property.1 ((EReal.coe_le_coe r.property.2).trans hdT.le)]
  exact (EReal.coe_le_coe r.property.2).trans_lt hdT

/-- Transfer the actual stopped Ito maximal estimate to C([0,d],R).
This transfer assumes only a bound already proved for the stopped path. -/
theorem finite_real_path_memLp_bound
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω)
    {T : EReal} [Fact (0 ≤ T)]
    (F : ClosedTime T → MeasurableSpace Ω) (hle : ∀ t, F t ≤ m)
    (Z : ClosedTime T → Ω → ℝ) (d : ℝ) (hdT : (d:EReal) < T)
    (hc : ∀ ω, Continuous (fun t => Z (min (realTimeClamp d) t) ω))
    (hZ : ∀ t, t < ⊤ → Measurable[F t] (Z t))
    (B : ℝ≥0∞) (hB : B < ∞)
    (hb : eLpNorm (continuousPath (fun t ω => Z (min (realTimeClamp d) t) ω) hc) 2 P ≤ B) :
    MemLp (finiteRealPath Z d hc) 2 P ∧ eLpNorm (finiteRealPath Z d hc) 2 P ≤ B := by
  have hm : AEStronglyMeasurable (finiteRealPath Z d hc) P :=
    (finite_real_path_measurable F hle Z d hdT hc hZ).aestronglyMeasurable
  have hnorm := (eLpNorm_mono_ae hm (Filter.Eventually.of_forall
    (finite_real_path_norm_le Z d hc))).trans hb
  exact ⟨hnorm.trans_lt hB,hnorm⟩

end Asakura.Chapter4

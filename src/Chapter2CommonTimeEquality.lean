import Chapter2LocalCovarianceRules

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- The last step of the printed covariation formula: continuous processes
which agree at each fixed time agree at all finite times outside one null set. -/
theorem continuous_process_common_time_equality
    {Ω D : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [TopologicalSpace D] [TopologicalSpace.SeparableSpace D] [Nonempty D]
    (X Y : D → Ω → ℝ) (hX : ∀ ω, Continuous (fun t => X t ω))
    (hY : ∀ ω, Continuous (fun t => Y t ω))
    (he : ∀ t, X t =ᵐ[P] Y t) :
    ∀ᵐ ω ∂P, ∀ t, X t ω = Y t ω := by
  let q := TopologicalSpace.denseSeq D
  have hq : ∀ᵐ ω ∂P, ∀ n, X (q n) ω = Y (q n) ω := ae_all_iff.mpr (fun n => he (q n))
  filter_upwards [hq] with ω hω
  have hfg : (fun t => X t ω) = (fun t => Y t ω) :=
    (hX ω).ext_on (TopologicalSpace.denseRange_denseSeq D) (hY ω)
      (fun t ht => by obtain ⟨n,rfl⟩ := ht; exact hω n)
  exact fun t => congrFun hfg t

theorem LocalCovarianceWitness.continuous_open_paths
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (X Y C : ClosedTime T → Ω → ℝ)
    (hX : LocalMProcessWitness P F X) (hY : LocalMProcessWitness P F Y)
    (hC : LocalCovarianceWitness P F X Y C) (ω : Ω) :
    Continuous (fun t : Iio (⊤ : ClosedTime T) => C t.val ω) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have h := ((hX.path P F ω t.val t.property).mul (hY.path P F ω t.val t.property)).sub
    (hC.defect.path P F ω t.val t.property)
  have hc : ContinuousAt (fun s => C s ω) t.val := by
    convert h using 1
    funext s
    dsimp only [Pi.sub_apply,Pi.mul_apply]
    ring
  exact hc.comp continuous_subtype_val.continuousAt

theorem local_covariance_common_time_equality
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω)
    (X Y C R : ClosedTime T → Ω → ℝ)
    (hX : LocalMProcessWitness P F X) (hY : LocalMProcessWitness P F Y)
    (hC : LocalCovarianceWitness P F X Y C)
    (hR : ∀ ω, Continuous (fun t : Iio (⊤ : ClosedTime T) => R t.val ω))
    (he : ∀ t, t < ⊤ → C t =ᵐ[P] R t) :
    ∀ᵐ ω ∂P, ∀ t, t < ⊤ → C t ω = R t ω := by
  letI : Nonempty (Iio (⊤ : ClosedTime T)) := ⟨⟨⊥,hT⟩⟩
  have h := continuous_process_common_time_equality P
    (fun t : Iio (⊤ : ClosedTime T) => C t.val)
    (fun t : Iio (⊤ : ClosedTime T) => R t.val)
    (hC.continuous_open_paths P F X Y C hX hY) hR (fun t => he t.val t.property)
  exact h.mono (fun ω hω t ht => hω ⟨t,ht⟩)

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.local_covariance_common_time_equality
